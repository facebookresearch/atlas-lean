/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.ChainComplex.TensorCoefficient
public import MathlibExt.Algebra.Homology.ChainComplex.HomologyZero
public import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
# Coefficient homology sequences of flat-term complexes

A coefficient short exact sequence and flat second-factor terms give a
short exact sequence of complexes. Its homology sequence supplies the
connecting map, consecutive exactness, naturality and lift computation.

Changes of the coefficient short exact sequence and of the flat-term
complex commute with the connecting map. Carrier universes are independent.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v t

namespace ChainComplex.TensorCoefficient

variable (R : Type u) [CommRing R] (K : ChainComplex (ModuleCat.{v} R) ℕ)

/-- Homology of the same native tensor-coefficient complex. -/
def homologyFunctor (n : ℕ) : ModuleCat.{t} R ⥤ ModuleCat.{max v t} R :=
  functor R K ⋙ HomologicalComplex.homologyFunctor
    (ModuleCat.{max v t} R) (ComplexShape.down ℕ) n

/-- Additivity comes from the actual coefficient and native homology functors. -/
instance homologyFunctor_additive (n : ℕ) : (homologyFunctor.{u, v, t} R K n).Additive := by
  change (functor.{u, v, t} R K ⋙ HomologicalComplex.homologyFunctor
    (ModuleCat.{max v t} R) (ComplexShape.down ℕ) n).Additive
  infer_instance

/-- The actual native connecting map; flatness is only imposed on the chain terms. -/
def connecting (hK : ∀ n, Module.Flat R (K.X n))
    (S : ShortComplex (ModuleCat.{t} R)) (hS : S.ShortExact) (n : ℕ) :
    (homologyFunctor R K (n + 1)).obj S.X₃ ⟶
      (homologyFunctor R K n).obj S.X₁ :=
  (shortExact R K hK S hS).δ (n + 1) n rfl

@[reassoc]
theorem connecting_comp (hK : ∀ n, Module.Flat R (K.X n))
    (S : ShortComplex (ModuleCat.{t} R)) (hS : S.ShortExact) (n : ℕ) :
    connecting R K hK S hS n ≫ (homologyFunctor R K n).map S.f = 0 :=
  (shortExact R K hK S hS).δ_comp (n + 1) n rfl

@[reassoc]
theorem comp_connecting (hK : ∀ n, Module.Flat R (K.X n))
    (S : ShortComplex (ModuleCat.{t} R)) (hS : S.ShortExact) (n : ℕ) :
    (homologyFunctor R K (n + 1)).map S.g ≫ connecting R K hK S hS n = 0 :=
  (shortExact R K hK S hS).comp_δ (n + 1) n rfl

/-- Exactness after the actual connecting morphism. -/
theorem exact₁ (hK : ∀ n, Module.Flat R (K.X n))
    (S : ShortComplex (ModuleCat.{t} R)) (hS : S.ShortExact) (n : ℕ) :
    (ShortComplex.mk (connecting R K hK S hS n)
      ((homologyFunctor R K n).map S.f)
      (connecting_comp R K hK S hS n)).Exact :=
  (shortExact R K hK S hS).homology_exact₁ (n + 1) n rfl

/-- Exactness of the three original coefficient groups, including degree zero. -/
theorem exact₂ (hK : ∀ n, Module.Flat R (K.X n))
    (S : ShortComplex (ModuleCat.{t} R)) (hS : S.ShortExact) (n : ℕ) :
    (S.map (homologyFunctor R K n)).Exact :=
  (shortExact R K hK S hS).homology_exact₂ n

/-- Exactness before the actual connecting morphism. -/
theorem exact₃ (hK : ∀ n, Module.Flat R (K.X n))
    (S : ShortComplex (ModuleCat.{t} R)) (hS : S.ShortExact) (n : ℕ) :
    (ShortComplex.mk ((homologyFunctor R K (n + 1)).map S.g)
      (connecting R K hK S hS n) (comp_connecting R K hK S hS n)).Exact :=
  (shortExact R K hK S hS).homology_exact₃ (n + 1) n rfl

/-- Six consecutive terms retain all five actual maps of the native homology sequence. -/
def sixTermSequence (hK : ∀ n, Module.Flat R (K.X n))
    (S : ShortComplex (ModuleCat.{t} R)) (hS : S.ShortExact) (n : ℕ) :
    ComposableArrows (ModuleCat.{max v t} R) 5 :=
  HomologicalComplex.HomologySequence.composableArrows₅
    (shortExact R K hK S hS) (n + 1) n rfl

theorem sixTermSequence_exact (hK : ∀ n, Module.Flat R (K.X n))
    (S : ShortComplex (ModuleCat.{t} R)) (hS : S.ShortExact) (n : ℕ) :
    (sixTermSequence R K hK S hS n).Exact :=
  HomologicalComplex.HomologySequence.composableArrows₅_exact
    (shortExact R K hK S hS) (n + 1) n rfl

/-- A map of the original coefficient sequences commutes with the connecting map. -/
theorem connecting_naturality_sequence (hK : ∀ n, Module.Flat R (K.X n))
    {S T : ShortComplex (ModuleCat.{t} R)} (f : S ⟶ T)
    (hS : S.ShortExact) (hT : T.ShortExact) (n : ℕ) :
    connecting R K hK S hS n ≫ (homologyFunctor R K n).map f.τ₁ =
      (homologyFunctor R K (n + 1)).map f.τ₃ ≫ connecting R K hK T hT n :=
  HomologicalComplex.HomologySequence.δ_naturality
    ((functor R K).mapShortComplex.map f)
    (shortExact R K hK S hS) (shortExact R K hK T hT) (n + 1) n rfl

/-- The entire six-term sequence is natural for the original coefficient-sequence map. -/
def sixTermSequenceMap (hK : ∀ n, Module.Flat R (K.X n))
    {S T : ShortComplex (ModuleCat.{t} R)} (f : S ⟶ T)
    (hS : S.ShortExact) (hT : T.ShortExact) (n : ℕ) :
    sixTermSequence R K hK S hS n ⟶ sixTermSequence R K hK T hT n :=
  HomologicalComplex.HomologySequence.mapComposableArrows₅
    ((functor R K).mapShortComplex.map f)
    (shortExact R K hK S hS) (shortExact R K hK T hT) (n + 1) n rfl

/-- A change of the actual second-factor complex gives the actual coefficient
short-complex map, with no chosen comparison or homology square as an input. -/
def mapShortComplex {L : ChainComplex (ModuleCat.{v} R) ℕ} (f : K ⟶ L)
    (S : ShortComplex (ModuleCat.{t} R)) :
    S.map (functor R K) ⟶ S.map (functor R L) :=
  S.mapNatTrans (map R f)

/-- Native naturality in the actual second-factor chain map. -/
theorem connecting_naturality_complex
    {L : ChainComplex (ModuleCat.{v} R) ℕ} (f : K ⟶ L)
    (hK : ∀ n, Module.Flat R (K.X n)) (hL : ∀ n, Module.Flat R (L.X n))
    (S : ShortComplex (ModuleCat.{t} R)) (hS : S.ShortExact) (n : ℕ) :
    connecting R K hK S hS n ≫
        HomologicalComplex.homologyMap ((map R f).app S.X₁) n =
      HomologicalComplex.homologyMap ((map R f).app S.X₃) (n + 1) ≫
        connecting R L hL S hS n :=
  HomologicalComplex.HomologySequence.δ_naturality (mapShortComplex R K f S)
    (shortExact R K hK S hS) (shortExact R L hL S hS) (n + 1) n rfl

/-- The connective sequence ends at the actual surjective H₀ coefficient map. -/
theorem homologyMap_zero_epi (hK : ∀ n, Module.Flat R (K.X n))
    (S : ShortComplex (ModuleCat.{t} R)) (hS : S.ShortExact) :
    Epi ((homologyFunctor R K 0).map S.g) := by
  let K₂ := (functor R K).obj S.X₂
  let K₃ := (functor R K).obj S.X₃
  let g : K₂ ⟶ K₃ := (functor R K).map S.g
  have hZero := (HomologicalComplex.shortExact_iff_degreewise_shortExact
    (S.map (functor R K))).mp (shortExact R K hK S hS) 0
  letI : Epi (g.f 0) := hZero.epi_g
  letI : Epi (ChainComplex.homologyZeroClass K₃) := by
    unfold ChainComplex.homologyZeroClass
    infer_instance
  letI : Epi (ChainComplex.homologyZeroClass K₂ ≫ HomologicalComplex.homologyMap g 0) := by
    rw [ChainComplex.homologyZeroClass_naturality]
    infer_instance
  exact epi_of_epi (ChainComplex.homologyZeroClass K₂) (HomologicalComplex.homologyMap g 0)

/-- Native lift computation of the connecting map. The hypotheses are genuine
cycle, lift, and boundary equations in the displayed original complexes. -/
theorem connecting_eq (hK : ∀ n, Module.Flat R (K.X n))
    (S : ShortComplex (ModuleCat.{t} R)) (hS : S.ShortExact) (n : ℕ)
    {T : ModuleCat.{max v t} R}
    (x₃ : T ⟶ ((functor R K).obj S.X₃).X (n + 1))
    (hx₃ : x₃ ≫ ((functor R K).obj S.X₃).d (n + 1) n = 0)
    (x₂ : T ⟶ ((functor R K).obj S.X₂).X (n + 1))
    (hx₂ : x₂ ≫ ((functor R K).map S.g).f (n + 1) = x₃)
    (x₁ : T ⟶ ((functor R K).obj S.X₁).X n)
    (hx₁ : x₁ ≫ ((functor R K).map S.f).f n =
      x₂ ≫ ((functor R K).obj S.X₂).d (n + 1) n) :
    ((functor R K).obj S.X₃).liftCycles x₃ n
      ((ComplexShape.down ℕ).next_eq' (show (ComplexShape.down ℕ).Rel (n + 1) n from rfl)) hx₃ ≫
        ((functor R K).obj S.X₃).homologyπ (n + 1) ≫
          connecting R K hK S hS n =
      ((functor R K).obj S.X₁).liftCycles x₁ ((ComplexShape.down ℕ).next n) rfl
        (by
          let h := shortExact R K hK S hS
          have hDegree := (HomologicalComplex.shortExact_iff_degreewise_shortExact
            (S.map (functor R K))).mp h ((ComplexShape.down ℕ).next n)
          let : Mono (((functor R K).map S.f).f ((ComplexShape.down ℕ).next n)) := hDegree.mono_f
          rw [← cancel_mono (((functor R K).map S.f).f ((ComplexShape.down ℕ).next n)),
            Category.assoc, ← HomologicalComplex.Hom.comm, reassoc_of% hx₁,
            HomologicalComplex.d_comp_d, CategoryTheory.Limits.comp_zero, CategoryTheory.Limits.zero_comp]) ≫
        ((functor R K).obj S.X₁).homologyπ n :=
  (shortExact R K hK S hS).δ_eq (n + 1) n rfl x₃ hx₃ x₂ hx₂ x₁ hx₁
    ((ComplexShape.down ℕ).next n) rfl

end ChainComplex.TensorCoefficient

end
