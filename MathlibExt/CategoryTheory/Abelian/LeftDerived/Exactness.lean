/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Abelian.LeftDerived.LongExact
public import MathlibExt.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# Exactness detected by the first left-derived functor

Let `C,D` be abelian, with projective resolutions in `C`, and
`F : C → D` additive. Homology preservation forces all positive
left-derived values to vanish. If `F` preserves finite colimits,
vanishing of `L₁F` on every object is equivalent to preservation
of finite limits. For one short exact sequence, vanishing of `L₁F`
on its quotient suffices to make the mapped sequence short exact.
-/

@[expose] public section
noncomputable section

open CategoryTheory Category Limits

universe u₁ v₁ u₂ v₂

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasProjectiveResolutions C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]
  (F : C ⥤ D) [F.Additive]

/-- Let `C,D` be abelian, with projective resolutions in `C`,
and `F : C → D` additive. If `F` preserves homology, `L_(n+1)F(X)` is zero for every
object `X` and every `n ∈ ℕ`. -/
theorem isZero_leftDerived_obj_succ_of_preservesHomology [F.PreservesHomology]
    (X : C) (n : ℕ) : IsZero ((F.leftDerived (n + 1)).obj X) := by
  let P := projectiveResolution X
  have hP : IsZero (P.complex.homology (n + 1)) :=
    (P.complex_exactAt_succ n).isZero_homology
  let eH : ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).homology
      (n + 1) ≅ F.obj (P.complex.homology (n + 1)) :=
    (HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.down ℕ) (n + 1) F).app
      P.complex
  let e : (F.leftDerived (n + 1)).obj X ≅ F.obj (P.complex.homology (n + 1)) :=
    P.isoLeftDerivedObj F (n + 1) ≪≫ eH
  exact (F.map_isZero hP).of_iso e

/-- Let `C,D` be abelian, with projective resolutions in `C`,
and `F : C → D` additive. For short exact `S : X₁ → X₂ → X₃`, if
`L_(n+1)F(X₃)=0` and `L_nF(X₂)=0`, then `L_nF(X₁)=0`,
by the exact window ending in the left object. -/
theorem isZero_leftDerived_obj_of_shortExact (n : ℕ)
    {S : ShortComplex C} (hS : S.ShortExact)
    (h₃ : IsZero ((F.leftDerived (n + 1)).obj S.X₃))
    (h₂ : IsZero ((F.leftDerived n).obj S.X₂)) :
    IsZero ((F.leftDerived n).obj S.X₁) := by
  obtain ⟨hw, hExact⟩ := LeftDerivedDelta.LDexact_A F n S hS
  have hδ : LeftDerivedDelta.LDdelta F n S hS = 0 := h₃.eq_of_src _ 0
  let A := ShortComplex.mk (LeftDerivedDelta.LDdelta F n S hS)
    ((F.leftDerived n).map S.f) hw
  have hA : A.Exact := hExact
  letI : Mono ((F.leftDerived n).map S.f) := (A.exact_iff_mono hδ).1 hA
  exact IsZero.of_mono ((F.leftDerived n).map S.f) h₂

variable [PreservesFiniteColimits F]

/-- Let `C,D` be abelian, with projective resolutions in `C`,
and `F : C → D` additive. Suppose `F` preserves finite colimits. For short exact `S : X₁ → X₂ →
X₃`, if `L₁F(X₃)=0`,
the sequence `F(X₁) → F(X₂) → F(X₃)` is short exact. -/
theorem _root_.CategoryTheory.ShortComplex.ShortExact.map_of_isZero_leftDerived_one
    {S : ShortComplex C} (hS : S.ShortExact)
    (h₁ : IsZero ((F.leftDerived 1).obj S.X₃)) : (S.map F).ShortExact := by
  have hRight := (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi F).1
    (inferInstance : PreservesFiniteColimits F) S hS
  obtain ⟨hw, hA⟩ := LeftDerivedDelta.LDexact_A F 0 S hS
  let T : C ⥤ D := F.leftDerived 0
  let δ : (F.leftDerived 1).obj S.X₃ ⟶ T.obj S.X₁ :=
    LeftDerivedDelta.LDdelta F 0 S hS
  have hδ : δ = 0 := h₁.eq_of_src _ 0
  let A := ShortComplex.mk δ (T.map S.f) hw
  have hA' : A.Exact := hA
  have hMono : Mono (T.map S.f) := (A.exact_iff_mono hδ).1 hA'
  letI := hMono
  let e : T ≅ F := F.leftDerivedZeroIsoSelf
  let a : T.obj S.X₁ ≅ F.obj S.X₁ := e.app S.X₁
  let b : T.obj S.X₂ ≅ F.obj S.X₂ := e.app S.X₂
  have ht : T.map S.f ≫ b.hom = a.hom ≫ F.map S.f := e.hom.naturality S.f
  have hf : F.map S.f = a.inv ≫ T.map S.f ≫ b.hom :=
    (a.inv_hom_id_assoc (F.map S.f)).symm.trans
      (congrArg (fun t : T.obj S.X₁ ⟶ F.obj S.X₂ => a.inv ≫ t) ht.symm)
  have hMonoF : Mono (F.map S.f) := by
    rw [hf]
    infer_instance
  exact ShortComplex.ShortExact.mk' hRight.1 hMonoF hRight.2

/-- Let `C,D` be abelian, with projective resolutions in `C`,
and `F : C → D` additive. Suppose `F` preserves finite colimits. If `L₁F(X)=0` for every object
`X`, then `F` preserves
finite limits and hence is left exact. -/
theorem preservesFiniteLimits_of_isZero_leftDerived_one
    (h₁ : ∀ X : C, IsZero ((F.leftDerived 1).obj X)) : PreservesFiniteLimits F := by
  apply (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono F).2
  intro S hS
  have hMapped := ShortComplex.ShortExact.map_of_isZero_leftDerived_one F hS (h₁ S.X₃)
  exact ⟨hMapped.exact, hMapped.mono_f⟩

/-- Let `C,D` be abelian, with projective resolutions in `C`,
and `F : C → D` additive. Suppose `F` preserves finite colimits. The functor `F` preserves finite
limits if and only if
`L₁F(X)=0` for every object `X`. -/
theorem preservesFiniteLimits_iff_isZero_leftDerived_one :
    PreservesFiniteLimits F ↔ ∀ X : C, IsZero ((F.leftDerived 1).obj X) := by
  constructor
  · intro h X
    letI := h
    exact isZero_leftDerived_obj_succ_of_preservesHomology F X 0
  · exact preservesFiniteLimits_of_isZero_leftDerived_one F

end CategoryTheory.Functor
