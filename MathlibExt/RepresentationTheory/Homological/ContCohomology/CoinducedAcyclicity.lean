/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic
public import Mathlib.Topology.CompactOpen
public import MathlibExt.Algebra.Category.ModuleCat.Topology.Homology
public import MathlibExt.Algebra.Category.ModuleCat.Topology.Zero

/-!
# Positive acyclicity of compact-open coinduction

Let R be a ring with a topology, G a locally compact topological group,
and X a topological R-representation of G. The coinduced coefficient
C(G,X) has compact-open topology and diagonal action
(g • F)(x) = g • F(g⁻¹x).

Diagonal evaluation supplies an extra degeneracy of its homogeneous
resolution. The signed contraction makes Hⁿ_cts(G,Coind(X)) a zero
object for every n > 0. The scalar, group and coefficient universes
are independent, and X need not have discrete topology.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open CategoryTheory CategoryTheory.Limits ContRepresentation

universe u v w z

namespace ContinuousCohomology

variable {k : Type u} {G : Type v}
variable [Ring k] [TopologicalSpace k]
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [LocallyCompactSpace G]

private def coindOneEval
    (X : TopRep.{max v w, u, v} k G) :
    C(G, X) →L[k] X :=
  ContinuousMap.evalCLM k 1

omit [LocallyCompactSpace G] in
private theorem coindOneEval_comp_iota
    (X : TopRep.{max v w, u, v} k G) :
    (coindOneEval X).comp X.ρ.coind₁ι.toContinuousLinearMap =
      ContinuousLinearMap.id k X := by
  ext x
  rfl

omit [LocallyCompactSpace G] in
private theorem coindOneIota_injective
    (X : TopRep.{max v w, u, v} k G) :
    Function.Injective X.ρ.coind₁ι :=
  fun x y hxy => by
    have h := congrArg (fun F => coindOneEval X F) hxy
    change x = y at h
    exact h

private def coindOneDiagonal
    (X : TopRep.{max v w, u, v} k G) :
    X.coind₁.coind₁ ⟶ X.coind₁ :=
  TopRep.ofHom
    { toFun := fun F =>
        ⟨fun x => F x x,
          continuous_eval.comp
            (F.continuous.prodMk continuous_id)⟩
      map_add' := by
        intro F H
        ext x
        rfl
      map_smul' := by
        intro r F
        ext x
        rfl
      cont := by
        apply ContinuousMap.continuous_of_continuous_uncurry
        have h₁ : Continuous
            (fun p : C(G, C(G, X)) × G => p.1 p.2) :=
          continuous_eval
        exact continuous_eval.comp
          (h₁.prodMk continuous_snd)
      isIntertwining' := by
        intro g
        ext F x
        rfl }

@[simp]
private theorem coindOneDiagonal_apply
    (X : TopRep.{max v w, u, v} k G)
    (F : C(G, C(G, X))) (x : G) :
    (coindOneDiagonal X).hom F x = F x x :=
  rfl

private def coindOneDiagonalIter
    (X : TopRep.{max v w, u, v} k G) :
    (n : ℕ) →
      TopRep.resolutionX X.coind₁ (n + 1) ⟶
        TopRep.resolutionX X.coind₁ n
  | 0 => coindOneDiagonal X
  | n + 1 => (TopRep.coind₁Functor k G).map
      (coindOneDiagonalIter X n)

private theorem coindOneDiagonalIter_succ
    (X : TopRep.{max v w, u, v} k G) (n : ℕ) :
    coindOneDiagonalIter X (n + 1) =
      (TopRep.coind₁Functor k G).map
        (coindOneDiagonalIter X n) :=
  rfl

@[reassoc (attr := simp)]
private theorem coindOneIota_comp_diagonal
    (X : TopRep.{max v w, u, v} k G) :
    TopRep.ofHom X.ρ.coind₁.coind₁ι ≫ coindOneDiagonal X = 𝟙 X.coind₁ := by
  ext F x
  rfl

private theorem coindOneDiagonalIter_d_sub_zero
    (X : TopRep.{max v w, u, v} k G) :
    coindOneDiagonalIter X 0 ≫ TopRep.d X.coind₁ 0 -
        TopRep.d X.coind₁ 1 ≫ coindOneDiagonalIter X 1 =
      𝟙 (TopRep.resolutionX X.coind₁ 1) := by
  apply TopRep.hom_ext
  ext F x y
  change F y y - (F y y - F x y) = F x y
  abel

private theorem sub_sub_same {A : Type*} [AddCommGroup A]
    (a b d : A) : a - b - (a - d) = d - b := by
  abel

private theorem coindOneDiagonalIter_d_sub
    (X : TopRep.{max v w, u, v} k G) (n : ℕ) :
    coindOneDiagonalIter X n ≫ TopRep.d X.coind₁ n -
        TopRep.d X.coind₁ (n + 1) ≫ coindOneDiagonalIter X (n + 1) =
      (-1 : ℤ) ^ n • 𝟙 (TopRep.resolutionX X.coind₁ (n + 1)) := by
  induction n with
  | zero =>
      simpa using coindOneDiagonalIter_d_sub_zero.{u, v, w} X
  | succ n ih =>
      let C := TopRep.coind₁Functor k G
      rw [TopRep.d_succ, TopRep.d_succ]
      simp only [coindOneDiagonalIter_succ, Preadditive.comp_sub,
        Preadditive.sub_comp]
      have hnat := TopRep.coind₁ι.naturality
        (C.map (coindOneDiagonalIter X n))
      change
        TopRep.ofHom (ContRepresentation.coind₁Map
            (coindOneDiagonalIter X n).hom) ≫
              TopRep.ofHom
                (TopRep.resolutionX X.coind₁ n).ρ.coind₁.coind₁ι =
          TopRep.ofHom
              (TopRep.resolutionX X.coind₁ n).ρ.coind₁.coind₁.coind₁ι ≫
            TopRep.ofHom (ContRepresentation.coind₁Map
              (TopRep.ofHom (ContRepresentation.coind₁Map
                (coindOneDiagonalIter X n).hom)).hom) at hnat
      rw [hnat]
      have hcomp₁ :
          TopRep.ofHom (ContRepresentation.coind₁Map
              (coindOneDiagonalIter X n).hom) ≫
            TopRep.ofHom (ContRepresentation.coind₁Map
              (TopRep.d X.coind₁ n).hom) =
          C.map (coindOneDiagonalIter X n ≫
            TopRep.d X.coind₁ n) := by
        exact (C.map_comp _ _).symm
      have hcomp₂ :
          TopRep.ofHom (ContRepresentation.coind₁Map
              (TopRep.d X.coind₁ (n + 1)).hom) ≫
            TopRep.ofHom (ContRepresentation.coind₁Map
              (TopRep.ofHom (ContRepresentation.coind₁Map
                (coindOneDiagonalIter X n).hom)).hom) =
          C.map (TopRep.d X.coind₁ (n + 1) ≫
            C.map (coindOneDiagonalIter X n)) := by
        exact (C.map_comp _ _).symm
      rw [hcomp₁, hcomp₂]
      rw [sub_sub_same]
      rw [← C.map_sub]
      have ih' :
          TopRep.d X.coind₁ (n + 1) ≫
                C.map (coindOneDiagonalIter X n) -
              coindOneDiagonalIter X n ≫ TopRep.d X.coind₁ n =
            -((-1 : ℤ) ^ n •
              𝟙 (TopRep.resolutionX X.coind₁ (n + 1))) := by
        rw [← coindOneDiagonalIter_succ]
        rw [← neg_sub, ih]
      rw [ih', C.map_neg, C.map_zsmul, C.map_id]
      simp [pow_succ]
      rfl

private theorem continuousCohomology_eq_zero_coind_succ
    (X : TopRep.{max v w, u, v} k G) (n : ℕ)
    (x : continuousCohomology (n + 1) X.coind₁) : x = 0 := by
  let K := TopRep.homogeneousCochains X.coind₁
  obtain ⟨z, rfl⟩ := K.homologyπ_surjective n (n + 1) (by simp) x
  rw [K.homologyπ_eq_zero_iff_exists_boundary n (n + 1) (by simp) z]
  let v : K.X (n + 1) := (K.iCycles (n + 1)).hom z
  let s := coindOneDiagonalIter X (n + 1)
  let sign : ℤ := (-1 : ℤ) ^ (n + 1)
  let b₀ : K.X n :=
    ((TopRep.invariantsFunctor k G).map s).hom v
  let b : K.X n := sign • b₀
  refine ⟨b, ?_⟩
  apply Subtype.ext
  have hz := ConcreteCategory.congr_hom
    (K.iCycles_d (n + 1) (n + 2)) z
  have hrel := ConcreteCategory.congr_hom
    (coindOneDiagonalIter_d_sub X (n + 1)) v.1
  change (K.d (n + 1) (n + 2)).hom v = 0 at hz
  change v.1 = ((K.d n (n + 1)).hom b).1
  have hzval : ((K.d (n + 1) (n + 2)).hom v).1 = 0 :=
    congrArg Subtype.val hz
  have hdout := TopRep.homogeneousCochains.d_apply
    X.coind₁ (n + 1) v
  have hzraw :
      (TopRep.d X.coind₁ (n + 2)).hom v.1 = 0 := by
    rw [← hdout]
    exact hzval
  have hdin := TopRep.homogeneousCochains.d_apply
    X.coind₁ n b₀
  have hdinraw :
      ((K.d n (n + 1)).hom b₀).1 =
        (TopRep.d X.coind₁ (n + 1)).hom (s.hom v.1) := by
    rw [hdin]
    rfl
  dsimp only [b]
  rw [map_zsmul]
  change v.1 = sign • ((K.d n (n + 1)).hom b₀).1
  rw [hdinraw]
  change
    (TopRep.d X.coind₁ (n + 1)).hom (s.hom v.1) -
        (coindOneDiagonalIter X (n + 2)).hom
          ((TopRep.d X.coind₁ (n + 2)).hom v.1) =
      (-1 : ℤ) ^ (n + 1) • v.1 at hrel
  rw [hzraw, map_zero, sub_zero] at hrel
  dsimp only [sign]
  rw [hrel]
  rw [← mul_smul, ← pow_add,
    (Even.add_self (n + 1)).neg_one_pow, one_smul]

/-- Let R be a ring equipped with a topology and G a topological
group. A coefficient X is a topological R-module with a G-representation
by continuous R-linear maps. Scalar, group and carrier universes are independent.
Write Coind(X) = C(G,X) with compact-open topology and diagonal action
(g • F)(x) = g • F(g⁻¹x).
If G is locally compact, then for every n ∈ ℕ the topological
continuous cohomology module Hⁿ⁺¹_cts(G,Coind(X)) is a zero object.
The coinduction and cohomology use this same group G. -/
theorem isZero_coind₁_succ
    (X : TopRep.{max v w, u, v} k G) (n : ℕ) :
    Limits.IsZero (continuousCohomology (n + 1) X.coind₁) := by
  let _ : Subsingleton (continuousCohomology (n + 1) X.coind₁) :=
    ⟨fun a b =>
      (continuousCohomology_eq_zero_coind_succ X n a).trans
        (continuousCohomology_eq_zero_coind_succ X n b).symm⟩
  exact TopModuleCat.isZero_of_subsingleton _

end ContinuousCohomology
