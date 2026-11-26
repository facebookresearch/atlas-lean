/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The proof of `epi_toSheaf_map_of_epi` below is adapted from
`MathlibExt.AlgebraicGeometry.SchemeModulesEpi` (which records its own upstream source).
-/
module

public import MathlibExt.AlgebraicGeometry.RightVFiltrationModels
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Presheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic.Ring

/-!
# Actual local nilpotence of the graded Euler operator

The Euler nilpotence hypothesis on the original `V`-filtration pieces yields local
nilpotence of the graded Euler endomorphism on every native graded piece. The right
Euler operator preserves each `V` piece because its finite-order operator preserves
every power of the coordinate ideal, so its iterates descend through the graded
projection and land in the positive-index union, which the projection kills.
Arbitrary graded sections are locally projections of lifts since the graded
projection is an epimorphism, hence locally surjective.

Source: Saito1307.2140v5, Sections1.1--1.5,2.1,2.2 and2.4.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.RightHodgeSourceRequests

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite TopologicalSpace
open MathlibExt.AlgebraicGeometry.RightDifferentialModules
open MathlibExt.AlgebraicGeometry.RightCoordinateDifferentials
open MathlibExt.AlgebraicGeometry.RightVFiltrationModels
open MathlibExt.AlgebraicGeometry.DifferentialOperatorSheaves
open MathlibExt.AlgebraicGeometry.DifferentialOperatorScalars

private theorem scalar_VOrderZero (k : Type) [CommRing k] (M : Type)
    [TopologicalSpace M] (O : (Opens M)ᵒᵖ ⥤ CommAlgCat.{0} k)
    (C : CoordinateDerivation k M O) (U : Opens M) (c : O.obj (op U)) :
    VOrderZero k M O C U (scalarFinite k M O U c) := by
  intro Vv r a
  refine ⟨(O.map (homOfLE Vv.property).op).hom c * a, ?_⟩
  change (O.map (homOfLE Vv.property).op).hom c * (C.function Vv.val ^ r * a) =
    C.function Vv.val ^ r * ((O.map (homOfLE Vv.property).op).hom c * a)
  ring

private theorem partialCoordinate_VOrderZero (k : Type) [CommRing k] (M : Type)
    [TopologicalSpace M] (O : (Opens M)ᵒᵖ ⥤ CommAlgCat.{0} k)
    (C : CoordinateDerivation k M O) (U : Opens M) :
    VOrderZero k M O C U
      (partialFinite k M O C U * coordinateFinite k M O C U) := by
  intro Vv r a
  refine ⟨C.function Vv.val * C.derivative Vv.val a + (r + 1) * a, ?_⟩
  have hpc : ∀ x : O.obj (op Vv.val),
      (partialFinite k M O C U * coordinateFinite k M O C U).val.val Vv x
        = C.derivative Vv.val (C.function Vv.val * x) := by
    intro x
    change C.derivative Vv.val ((coordinateFinite k M O C U).val.val Vv x) = _
    rw [coordinateFinite_apply]
  rw [hpc]
  have htr : C.function Vv.val * (C.function Vv.val ^ r * a)
      = C.function Vv.val ^ (r + 1) * a := by
    ring
  rw [htr]
  have hleib := (C.derivative Vv.val).leibniz (C.function Vv.val ^ (r + 1)) a
  rw [hleib]
  have hpow : C.derivative Vv.val (C.function Vv.val ^ (r + 1))
      = (r + 1) * C.function Vv.val ^ r := by
    have h := (C.derivative Vv.val).leibniz_pow (C.function Vv.val) (r + 1)
    rw [C.coordinate] at h
    rw [Nat.add_sub_cancel] at h
    simpa [smul_eq_mul, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] using h
  simp only [smul_eq_mul] at hleib ⊢
  rw [hpow]
  ring

private theorem add_VOrderZero (k : Type) [CommRing k] (M : Type)
    [TopologicalSpace M] (O : (Opens M)ᵒᵖ ⥤ CommAlgCat.{0} k)
    (C : CoordinateDerivation k M O) (U : Opens M)
    (P Q : finiteOperatorRing k M O U)
    (hP : VOrderZero k M O C U P) (hQ : VOrderZero k M O C U Q) :
    VOrderZero k M O C U (P + Q) := by
  intro Vv r a
  obtain ⟨b₁, hb₁⟩ := hP Vv r a
  obtain ⟨b₂, hb₂⟩ := hQ Vv r a
  refine ⟨b₁ + b₂, ?_⟩
  change P.val.val Vv (C.function Vv.val ^ r * a)
    + Q.val.val Vv (C.function Vv.val ^ r * a) = _
  rw [hb₁, hb₂, mul_add]

private theorem eulerFinite_VOrderZero (k : Type) [CommRing k] (M : Type)
    [TopologicalSpace M] (O : (Opens M)ᵒᵖ ⥤ CommAlgCat.{0} k)
    (C : CoordinateDerivation k M O) (U : Opens M) (c : k) :
    VOrderZero k M O C U (eulerFinite k M O C U c) :=
  add_VOrderZero k M O C U _ _ (partialCoordinate_VOrderZero k M O C U)
    (scalar_VOrderZero k M O C U _)

private theorem rightEuler_mem (k : Type) [CommRing k] [Algebra ℚ k] (M : Type)
    [TopologicalSpace M] (O : (Opens M)ᵒᵖ ⥤ CommAlgCat.{0} k)
    [HasSheafify (Opens.grothendieckTopology M) RingCat.{0}]
    (C : CoordinateDerivation k M O) (N : RightModule k M O)
    (V : RationalVFiltration k M O C N) (a : ℚ) (U : Opens M)
    (s : N.val.obj (op U)) (hs : s ∈ (V.term a).toSubmodule.obj (op U)) :
    rightEuler k M O C N U (algebraMap ℚ k a) s
      ∈ (V.term a).toSubmodule.obj (op U) :=
  V.zeroOrderAction a U (eulerFinite k M O C U (algebraMap ℚ k a))
    (eulerFinite_VOrderZero k M O C U (algebraMap ℚ k a)) s hs

private theorem eulerIterate_mem (k : Type) [CommRing k] [Algebra ℚ k] (M : Type)
    [TopologicalSpace M] (O : (Opens M)ᵒᵖ ⥤ CommAlgCat.{0} k)
    [HasSheafify (Opens.grothendieckTopology M) RingCat.{0}]
    (C : CoordinateDerivation k M O) (N : RightModule k M O)
    (V : RationalVFiltration k M O C N) (a : ℚ) (U : Opens M)
    (s : N.val.obj (op U)) (hs : s ∈ (V.term a).toSubmodule.obj (op U))
    (j : ℕ) :
    (rightEuler k M O C N U (algebraMap ℚ k a))^[j] s
      ∈ (V.term a).toSubmodule.obj (op U) := by
  induction j with
  | zero => exact hs
  | succ j ih =>
    simpa only [Function.iterate_succ_apply'] using
      rightEuler_mem k M O C N V a U _ ih

private theorem eulerIterate_projection (k : Type) [CommRing k] [Algebra ℚ k]
    (M : Type) [TopologicalSpace M] (O : (Opens M)ᵒᵖ ⥤ CommAlgCat.{0} k)
    [HasSheafify (Opens.grothendieckTopology M) RingCat.{0}]
    [HasSheafify (Opens.grothendieckTopology M) AddCommGrpCat.{0}]
    [(Opens.grothendieckTopology M).WEqualsLocallyBijective AddCommGrpCat.{0}]
    [∀ U : Opens M, HasWeakSheafify ((Opens.grothendieckTopology M).over U)
      AddCommGrpCat.{0}]
    [∀ U : Opens M, ((Opens.grothendieckTopology M).over U).WEqualsLocallyBijective
      AddCommGrpCat.{0}]
    (C : CoordinateDerivation k M O) (N : RightModule k M O)
    (V : RationalVFiltration k M O C N) (A : GradedVOperators k M O C N V)
    (a : ℚ) (U : Opens M) (t : (V.term a).toSheafOfModules.val.obj (op U))
    (j : ℕ) :
    (((A.eulerMap a).asHom.val.app (op U)).hom)^[j]
        (((gradedProjection k M O C N V a).val.app (op U)).hom t) =
      ((gradedProjection k M O C N V a).val.app (op U)).hom
        ⟨(rightEuler k M O C N U (algebraMap ℚ k a))^[j]
          (((V.term a).ι.val.app (op U)).hom t),
          eulerIterate_mem k M O C N V a U _ t.property j⟩ := by
  induction j with
  | zero => rfl
  | succ j ih =>
    conv_lhs => rw [Function.iterate_succ_apply']
    rw [ih]
    apply A.euler_normal
    change (rightEuler k M O C N U (algebraMap ℚ k a))^[j.succ]
      (((V.term a).ι.val.app (op U)).hom t) = _
    exact Function.iterate_succ_apply' _ _ _

private theorem projection_of_termAbove_eq_zero (k : Type) [CommRing k]
    [Algebra ℚ k] (M : Type) [TopologicalSpace M]
    (O : (Opens M)ᵒᵖ ⥤ CommAlgCat.{0} k)
    [HasSheafify (Opens.grothendieckTopology M) RingCat.{0}]
    [HasSheafify (Opens.grothendieckTopology M) AddCommGrpCat.{0}]
    [(Opens.grothendieckTopology M).WEqualsLocallyBijective AddCommGrpCat.{0}]
    [∀ U : Opens M, HasWeakSheafify ((Opens.grothendieckTopology M).over U)
      AddCommGrpCat.{0}]
    [∀ U : Opens M, ((Opens.grothendieckTopology M).over U).WEqualsLocallyBijective
      AddCommGrpCat.{0}]
    (C : CoordinateDerivation k M O) (N : RightModule k M O)
    (V : RationalVFiltration k M O C N) (a : ℚ) (U : Opens M)
    (u₀ : N.val.obj (op U)) (hterm : u₀ ∈ (V.term a).toSubmodule.obj (op U))
    (habove : u₀ ∈ (termAbove k M O C N V a).toSubmodule.obj (op U)) :
    ((gradedProjection k M O C N V a).val.app (op U)).hom ⟨u₀, hterm⟩ = 0 := by
  have hv : ((vStep k M O C N V a).val.app (op U)).hom ⟨u₀, habove⟩
      = ⟨u₀, hterm⟩ :=
    Subtype.ext rfl
  have h0 : vStep k M O C N V a ≫ gradedProjection k M O C N V a = 0 :=
    cokernel.condition _
  calc ((gradedProjection k M O C N V a).val.app (op U)).hom ⟨u₀, hterm⟩
      = ((gradedProjection k M O C N V a).val.app (op U)).hom
          (((vStep k M O C N V a).val.app (op U)).hom ⟨u₀, habove⟩) := by
        rw [hv]
    _ = (((vStep k M O C N V a ≫ gradedProjection k M O C N V a).val.app
          (op U)).hom ⟨u₀, habove⟩) := rfl
    _ = 0 := by
      rw [h0]
      rfl

private theorem epi_toSheaf_map_of_epi (k : Type) [CommRing k] (M : Type)
    [TopologicalSpace M] (O : (Opens M)ᵒᵖ ⥤ CommAlgCat.{0} k)
    [HasSheafify (Opens.grothendieckTopology M) RingCat.{0}]
    [HasSheafify (Opens.grothendieckTopology M) AddCommGrpCat.{0}]
    [(Opens.grothendieckTopology M).WEqualsLocallyBijective AddCommGrpCat.{0}]
    {M1 N1 : SheafOfModules.{0} (coefficientSheaf k M O)} (φ : M1 ⟶ N1)
    [Epi φ] :
    Epi ((SheafOfModules.toSheaf (coefficientSheaf k M O)).map φ) := by
  let adj :=
    PresheafOfModules.sheafificationAdjunction.{0} (𝟙 (coefficientSheaf k M O).obj)
  let G := SheafOfModules.forget.{0} (coefficientSheaf k M O) ⋙
    PresheafOfModules.restrictScalars (𝟙 (coefficientSheaf k M O).obj)
  let S := PresheafOfModules.sheafification.{0} (𝟙 (coefficientSheaf k M O).obj)
  let ψ := G.map φ
  have hcounit : IsIso adj.counit :=
    inferInstanceAs (IsIso (PresheafOfModules.sheafificationAdjunction.{0}
      (𝟙 (coefficientSheaf k M O).obj)).counit)
  let εM : S.obj (G.obj M1) ≅ M1 :=
    @asIso _ _ _ _ (adj.counit.app M1) (NatIso.isIso_app_of_isIso adj.counit M1)
  let εN : S.obj (G.obj N1) ≅ N1 :=
    @asIso _ _ _ _ (adj.counit.app N1) (NatIso.isIso_app_of_isIso adj.counit N1)
  have hnat : S.map ψ ≫ εN.hom = εM.hom ≫ φ := adj.counit.naturality φ
  have : Epi (S.map ψ) := by
    have hthis : S.map ψ = (εM.hom ≫ φ) ≫ εN.inv := (Iso.eq_comp_inv εN).2 hnat
    rw [hthis]
    infer_instance
  have h0 : S.map (cokernel.π ψ) = 0 := by
    apply zero_of_epi_comp (S.map ψ)
    rw [← S.map_comp, cokernel.condition]
    exact S.map_zero _ _
  let T := PresheafOfModules.toPresheaf (coefficientSheaf k M O).obj ⋙
    presheafToSheaf (Opens.grothendieckTopology M) AddCommGrpCat.{0}
  have hT : ∀ {P Q : PresheafOfModules.{0} (coefficientSheaf k M O).obj}
      (f : P ⟶ Q),
      T.map f = (SheafOfModules.toSheaf (coefficientSheaf k M O)).map (S.map f) :=
    fun f => rfl
  have h0' : T.map (cokernel.π ψ) = 0 := by
    rw [hT, h0]
    exact Functor.map_zero _ _ _
  have hc := isColimitOfHasCokernelOfPreservesColimit T ψ
  have hTψ : Epi (T.map ψ) := by
    refine Preadditive.epi_of_cancel_zero _ (fun g hg => ?_)
    obtain ⟨d, hd⟩ := CokernelCofork.IsColimit.desc' hc g hg
    rw [← hd]
    change T.map (cokernel.π ψ) ≫ d = 0
    rw [h0', zero_comp]
  have h2 : T.map ψ ≫
        ((SheafOfModules.toSheaf (coefficientSheaf k M O)).mapIso εN).hom =
      ((SheafOfModules.toSheaf (coefficientSheaf k M O)).mapIso εM).hom ≫
        (SheafOfModules.toSheaf (coefficientSheaf k M O)).map φ := by
    change (SheafOfModules.toSheaf (coefficientSheaf k M O)).map (S.map ψ) ≫
        (SheafOfModules.toSheaf (coefficientSheaf k M O)).map εN.hom =
      (SheafOfModules.toSheaf (coefficientSheaf k M O)).map εM.hom ≫
        (SheafOfModules.toSheaf (coefficientSheaf k M O)).map φ
    rw [← Functor.map_comp, ← Functor.map_comp, hnat]
  have hthis : (SheafOfModules.toSheaf (coefficientSheaf k M O)).map φ =
      ((SheafOfModules.toSheaf (coefficientSheaf k M O)).mapIso εM).inv ≫
        T.map ψ ≫
        ((SheafOfModules.toSheaf (coefficientSheaf k M O)).mapIso εN).hom :=
    (Iso.eq_inv_comp _).2 h2.symm
  rw [hthis]
  have : IsIso
      ((SheafOfModules.toSheaf (coefficientSheaf k M O)).mapIso εM).inv :=
    ((SheafOfModules.toSheaf (coefficientSheaf k M O)).mapIso εM).isIso_inv
  have : IsIso
      ((SheafOfModules.toSheaf (coefficientSheaf k M O)).mapIso εN).hom :=
    ((SheafOfModules.toSheaf (coefficientSheaf k M O)).mapIso εN).isIso_hom
  have h1 : Epi (T.map ψ ≫
      ((SheafOfModules.toSheaf (coefficientSheaf k M O)).mapIso εN).hom) :=
    epi_comp' hTψ (@IsIso.epi_of_iso _ _ _ _
      ((SheafOfModules.toSheaf (coefficientSheaf k M O)).mapIso εN).hom
      ((SheafOfModules.toSheaf (coefficientSheaf k M O)).mapIso εN).isIso_hom)
  exact epi_comp' (@IsIso.epi_of_iso _ _ _ _
    ((SheafOfModules.toSheaf (coefficientSheaf k M O)).mapIso εM).inv
    ((SheafOfModules.toSheaf (coefficientSheaf k M O)).mapIso εM).isIso_inv)
    h1

/-- The Euler nilpotence on original V lifts gives actual local nilpotence on the native grade. -/
theorem actual_graded_euler_local_nilpotence (k : Type) [CommRing k] [Algebra ℚ k]
    (M : Type) [TopologicalSpace M] (O : (Opens M)ᵒᵖ ⥤ CommAlgCat.{0} k)
    [HasSheafify (Opens.grothendieckTopology M) RingCat.{0}]
    [HasSheafify (Opens.grothendieckTopology M) AddCommGrpCat.{0}]
    [(Opens.grothendieckTopology M).WEqualsLocallyBijective AddCommGrpCat.{0}]
    [∀ U : Opens M, HasWeakSheafify ((Opens.grothendieckTopology M).over U)
      AddCommGrpCat.{0}]
    [∀ U : Opens M, ((Opens.grothendieckTopology M).over U).WEqualsLocallyBijective
      AddCommGrpCat.{0}]
    (C : CoordinateDerivation k M O) (N : RightModule k M O)
    (V : RationalVFiltration k M O C N) (A : GradedVOperators k M O C N V)
    (a : ℚ) (x : M) :
    ∃ U : Opens M, x ∈ U ∧ ∃ r : ℕ, 0 < r ∧
      ∀ (W : Opens M), W ≤ U → ∀ s : (gradedV k M O C N V a).val.obj (op W),
        ((((A.eulerMap a).asHom.val.app (op W)).hom)^[r]) s = 0 := by
  obtain ⟨U, hxU, r, hrpos, hnil⟩ := V.eulerNilpotent a x
  refine ⟨U, hxU, r, hrpos, ?_⟩
  intro W hWU s
  have hepi : Epi (gradedProjection k M O C N V a) := by
    change Epi (cokernel.π _)
    infer_instance
  have hepiS := epi_toSheaf_map_of_epi k M O
    (gradedProjection k M O C N V a)
  have : ConcreteCategory.HasFunctorialSurjectiveInjectiveFactorization
      AddCommGrpCat.{0} :=
    ⟨⟨ConcreteCategory.functorialSurjectiveInjectiveFactorizationData _⟩⟩
  have hlocS : Sheaf.IsLocallySurjective
      ((SheafOfModules.toSheaf (coefficientSheaf k M O)).map
        (gradedProjection k M O C N V a)) :=
    (Sheaf.isLocallySurjective_iff_epi'
      (φ := (SheafOfModules.toSheaf (coefficientSheaf k M O)).map
        (gradedProjection k M O C N V a))).2 inferInstance
  have hloc : Presheaf.IsLocallySurjective (Opens.grothendieckTopology M)
      ((PresheafOfModules.toPresheaf (coefficientSheaf k M O).obj).map
        (gradedProjection k M O C N V a).val) := hlocS
  have hsep : Presheaf.IsSeparated (Opens.grothendieckTopology M)
      (gradedV k M O C N V a).val.presheaf :=
    Presheaf.IsSheaf.isSeparated (gradedV k M O C N V a).isSheaf
  have hnat : ∀ (Y : Opens M) (f : Y ⟶ W)
      (x : (gradedV k M O C N V a).val.obj (op W)),
      ((gradedV k M O C N V a).val.map f.op).hom
          (((A.eulerMap a).asHom.val.app (op W)).hom x) =
        (((A.eulerMap a).asHom.val.app (op Y)).hom
          (((gradedV k M O C N V a).val.map f.op).hom x)) :=
    fun Y f x => (PresheafOfModules.naturality_apply
      (A.eulerMap a).asHom.val f.op x).symm
  have hcomm : ∀ (Y : Opens M) (f : Y ⟶ W)
      (x : (gradedV k M O C N V a).val.obj (op W)) (j : ℕ),
      ((gradedV k M O C N V a).val.map f.op).hom
          ((((A.eulerMap a).asHom.val.app (op W)).hom)^[j] x) =
        ((((A.eulerMap a).asHom.val.app (op Y)).hom)^[j]
          (((gradedV k M O C N V a).val.map f.op).hom x)) := by
    intro Y f x j
    induction j with
    | zero => rfl
    | succ j ih =>
      simp only [Function.iterate_succ_apply']
      rw [hnat, ih]
  have hkill : ∀ (Y : Opens M) (f : Y ⟶ W)
      (t : (V.term a).toSheafOfModules.val.obj (op Y)),
      (((A.eulerMap a).asHom.val.app (op Y)).hom)^[r]
        (((gradedProjection k M O C N V a).val.app (op Y)).hom t) = 0 := by
    intro Y f t
    have hYU : Y ≤ U := f.le.trans hWU
    have hB := eulerIterate_projection k M O C N V A a Y t r
    rw [hB]
    exact projection_of_termAbove_eq_zero k M O C N V a Y _
      (eulerIterate_mem k M O C N V a Y _ t.property r)
      (hnil Y hYU (((V.term a).ι.val.app (op Y)).hom t) t.property)
  refine hsep W (Presheaf.imageSieve ((PresheafOfModules.toPresheaf
    (coefficientSheaf k M O).obj).map (gradedProjection k M O C N V a).val) s)
    (Presheaf.imageSieve_mem (Opens.grothendieckTopology M)
      ((PresheafOfModules.toPresheaf (coefficientSheaf k M O).obj).map
        (gradedProjection k M O C N V a).val) (U := op W) s) _ 0 ?_
  intro Y f hf
  change ((gradedV k M O C N V a).val.map f.op).hom
      ((((A.eulerMap a).asHom.val.app (op W)).hom)^[r] s) =
    ((gradedV k M O C N V a).val.map f.op).hom 0
  have hlift := Presheaf.app_localPreimage
    ((PresheafOfModules.toPresheaf (coefficientSheaf k M O).obj).map
      (gradedProjection k M O C N V a).val) (U := op W) s (V := Y) f hf
  have hlift_coe : ((gradedProjection k M O C N V a).val.app (op Y))
      (Presheaf.localPreimage ((PresheafOfModules.toPresheaf
        (coefficientSheaf k M O).obj).map (gradedProjection k M O C N V a).val)
        (U := op W) s (V := Y) f hf) =
      (gradedV k M O C N V a).val.map f.op s := hlift
  have hlift2 : ((gradedProjection k M O C N V a).val.app (op Y)).hom
      (Presheaf.localPreimage ((PresheafOfModules.toPresheaf
        (coefficientSheaf k M O).obj).map (gradedProjection k M O C N V a).val)
        (U := op W) s (V := Y) f hf) =
      ((gradedV k M O C N V a).val.map f.op).hom s := hlift_coe
  rw [hcomm, ← hlift2, hkill Y f _, map_zero]

end WantedExt.AlgebraicGeometry.RightHodgeSourceRequests
