/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.RepresentationTheory.Homological.NormalizedBar.Linear

/-!
# Public consumers of normalized shuffle descent

The tuple API works with only a distinguished identity and independent
carrier universe. The actual shuffle square and identity-entry test use
an arbitrary group, without commutativity or a chosen normalization map.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped MonoidAlgebra

namespace Rep.NormalizedBar.LinearTests

universe v

section WeakTupleHypotheses

variable {G : Type v} [One G]

example {p q : ℕ} (a : Fin p → G) (b : Fin q → G)
    (σ : Equiv.Perm (Fin (p + q))) :
    Rep.NormalizedBar.IsNondegenerate G (Rep.NormalizedBar.interleave a b σ) ↔
      Rep.NormalizedBar.IsNondegenerate G a ∧ Rep.NormalizedBar.IsNondegenerate G b :=
  Rep.NormalizedBar.isNondegenerate_interleave_iff a b σ

example {p q : ℕ} (a : Rep.NormalizedBar.Tuple G p)
    (b : Rep.NormalizedBar.Tuple G q) (σ : Equiv.Perm (Fin (p + q)))
    (i : Fin (p + q)) :
    (Rep.NormalizedBar.interleaveTuple a b σ).val i ≠ 1 :=
  (Rep.NormalizedBar.interleaveTuple a b σ).property i

example {p q : ℕ} (a : Fin p → G) (b : Fin q → G) (i : Fin p) (hi : a i = 1)
    (σ : Equiv.Perm (Fin (p + q))) :
    ¬ Rep.NormalizedBar.IsNondegenerate G (Rep.NormalizedBar.interleave a b σ) :=
  Rep.NormalizedBar.interleave_degenerate_left a b σ (fun h => h i hi)

end WeakTupleHypotheses

section IndependentGroupUniverse

variable (G : Type v) [Group G]

open Classical in
/-- The coefficient order and sign formula do not require a small or commutative group. -/
example (p q : ℕ) (a : Fin p → G) (b : Fin q → G)
    (ha hb : G) (ca cb : ℤ) :
    shuffleLinear G p q
        (Finsupp.single a (MonoidAlgebra.single ha ca) ⊗ₜ[ℤ]
          Finsupp.single b (MonoidAlgebra.single hb cb)) =
      (ca * cb) •
        ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin (p + q)) =>
          AlgebraicTopology.EilenbergZilber.IsShuffle (p := p) (q := q) σ),
          ((Equiv.Perm.sign σ : ℤˣ) : ℤ) •
            Finsupp.single (interleave a b σ)
              (MonoidAlgebra.single (ha * hb) (1 : ℤ)) :=
  shuffleLinear_basis G p q a b ha hb ca cb

/-- The actual raw quotient square works in the independent group universe. -/
example (p q : ℕ) :
    (normalizedShuffleLinear G p q).comp
        (TensorProduct.map (rawProjection ℤ G p).hom.toLinearMap
          (rawProjection ℤ G q).hom.toLinearMap) =
      (rawProjection ℤ G (p + q)).hom.toLinearMap.comp (shuffleLinear G p q) :=
  normalizedShuffleLinear_desc G p q

/-- An empty left tuple does not prevent a right identity entry being killed. -/
example (ha hb : G) :
    (rawProjection ℤ G (0 + 1)).hom
      (shuffleLinear G 0 1
        (Finsupp.single (fun i : Fin 0 => i.elim0) (MonoidAlgebra.single ha 1) ⊗ₜ[ℤ]
          Finsupp.single (fun _ : Fin 1 => (1 : G)) (MonoidAlgebra.single hb 1))) = 0 :=
  shuffle_projection_zero_of_degenerate_right G 0 1
    (fun i : Fin 0 => i.elim0) (fun _ => 1) ha hb (fun h => h 0 rfl)

end IndependentGroupUniverse

section ActualNativeProjection

open Rep.NormalizedBar

variable (G : Type) [Group G]

example (p q : ℕ) :
    (normalizedShuffleLinear G p q).comp
        (TensorProduct.map ((Rep.NormalizedBar.nativeProjection ℤ G).f p).hom.toLinearMap
          ((Rep.NormalizedBar.nativeProjection ℤ G).f q).hom.toLinearMap) =
      ((Rep.NormalizedBar.nativeProjection ℤ G).f (p + q)).hom.toLinearMap.comp
        (shuffleLinear G p q) :=
  normalizedShuffleLinear_nativeProjection G p q

example (p q : ℕ) :
    normalizedShuffleLinear G p q =
      ((Rep.NormalizedBar.nativeProjection ℤ G).f (p + q)).hom.toLinearMap.comp
        ((shuffleLinear G p q).comp
          (TensorProduct.map ((Rep.NormalizedBar.nativeInclusion ℤ G).f p).hom.toLinearMap
            ((Rep.NormalizedBar.nativeInclusion ℤ G).f q).hom.toLinearMap)) :=
  normalizedShuffleLinear_nativeInclusion G p q

/-- A literal identity entry is killed by the actual native normalized projection. -/
example (q : ℕ) (b : Fin q → G) (ha hb : G) :
    ((Rep.NormalizedBar.nativeProjection ℤ G).f (1 + q)).hom
      (shuffleLinear G 1 q
        (Finsupp.single (fun _ : Fin 1 => (1 : G)) (MonoidAlgebra.single ha 1) ⊗ₜ[ℤ]
          Finsupp.single b (MonoidAlgebra.single hb 1))) = 0 := by
  have hdeg : ¬ Rep.NormalizedBar.IsNondegenerate G (fun _ : Fin 1 => (1 : G)) :=
    fun h => h 0 rfl
  let P : ((Fin (1 + q) → G) →₀ MonoidAlgebra ℤ G) →ₗ[ℤ]
      (Rep.NormalizedBar.Tuple G (1 + q) →₀ MonoidAlgebra ℤ G) :=
    ((Rep.NormalizedBar.nativeProjection ℤ G).f (1 + q)).hom.toLinearMap
  let x : (Fin (1 + q) → G) →₀ MonoidAlgebra ℤ G :=
    shuffleLinear G 1 q
      (Finsupp.single (fun _ : Fin 1 => (1 : G)) (MonoidAlgebra.single ha 1) ⊗ₜ[ℤ]
        Finsupp.single b (MonoidAlgebra.single hb 1))
  have hP : P = (Rep.NormalizedBar.rawProjection ℤ G (1 + q)).hom.toLinearMap :=
    congrArg
      (fun f : Rep.NormalizedBar.fullDegree ℤ G (1 + q) ⟶
          Rep.NormalizedBar.degree ℤ G (1 + q) => f.hom.toLinearMap)
      (Rep.NormalizedBar.nativeProjection_f ℤ G (1 + q))
  have hzero : (Rep.NormalizedBar.rawProjection ℤ G (1 + q)).hom.toLinearMap x = 0 :=
    shuffle_projection_zero_of_degenerate_left G 1 q (fun _ => 1) b ha hb hdeg
  change P x = 0
  exact (congrArg
    (fun f : ((Fin (1 + q) → G) →₀ MonoidAlgebra ℤ G) →ₗ[ℤ]
      (Rep.NormalizedBar.Tuple G (1 + q) →₀ MonoidAlgebra ℤ G) => f x) hP).trans hzero

/-- An operator satisfying the real projection square is forced to be the constructed one. -/
example (p q : ℕ)
    (F : TensorProduct ℤ ((Rep.NormalizedBar.complex ℤ G).X p).V
      ((Rep.NormalizedBar.complex ℤ G).X q).V →ₗ[ℤ]
        ((Rep.NormalizedBar.complex ℤ G).X (p + q)).V)
    (hF : F.comp
        (TensorProduct.map (Rep.NormalizedBar.rawProjection ℤ G p).hom.toLinearMap
          (Rep.NormalizedBar.rawProjection ℤ G q).hom.toLinearMap) =
      (Rep.NormalizedBar.rawProjection ℤ G (p + q)).hom.toLinearMap.comp
        (shuffleLinear G p q)) :
    F = normalizedShuffleLinear G p q :=
  normalizedShuffleLinear_unique G p q F hF

end ActualNativeProjection

end Rep.NormalizedBar.LinearTests

end
