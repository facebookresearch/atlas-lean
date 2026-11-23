/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.NativeRegularPathCoefficients
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import MathlibExt.AlgebraicTopology.LocalCoefficient.SSet
public import Mathlib.Logic.Equiv.Sum
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.CategoryTheory.NatIso
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
public import MathlibExt.AlgebraicTopology.LocalCoefficient.NervePullbackBarBaseFunctoriality
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.FreeAbelianGroup.Finsupp
public import Mathlib.Algebra.MonoidAlgebra.Module
public import MathlibExt.AlgebraicTopology.LocalCoefficient.TopCatBaseFunctoriality
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

/-!
# Actual pullback path indices for original regular coefficients

The first-vertex endpoint is computed from the actual map of fundamental
groupoids. The original coefficient degree object is compared with the
independently specified generators of the literal pulled-back cover.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

universe u v

namespace CategoryTheory

/-- The proposed integral path-basis cofan preserves the path-index universe. -/
noncomputable def integralPathBasisCofan (I : Type u) :
    Limits.Cofan (fun _ : I => AddCommGrpCat.of (ULift.{u} ℤ)) :=
  Limits.Cofan.mk (AddCommGrpCat.of (FreeAbelianGroup I)) fun i =>
    AddCommGrpCat.ofHom (uliftZMultiplesHom (FreeAbelianGroup I) (FreeAbelianGroup.of i))

/-- The ith integral summand sends every coefficient to that coefficient
times its path generator. -/
theorem integralPathBasisCofan_inj (I : Type u) (i : I) (z : ULift.{u} ℤ) :
    (integralPathBasisCofan I).inj i z = z.down • FreeAbelianGroup.of i := by
  change uliftZMultiplesHom (FreeAbelianGroup I) (FreeAbelianGroup.of i) z = _
  exact uliftZMultiplesHom_apply_apply (FreeAbelianGroup I) (FreeAbelianGroup.of i) z

/-- The universal candidate sends each free path generator to its actual integral unit inclusion. -/
noncomputable def integralPathBasisDesc {I : Type u}
    (s : Limits.Cofan (fun _ : I => AddCommGrpCat.of (ULift.{u} ℤ))) :
    AddCommGrpCat.of (FreeAbelianGroup I) ⟶ s.pt :=
  AddCommGrpCat.ofHom (FreeAbelianGroup.lift fun i => s.inj i (ULift.up (1 : ℤ)))

/-- The candidate desc map has the required unit-generator formula. -/
theorem integralPathBasisDesc_of {I : Type u}
    (s : Limits.Cofan (fun _ : I => AddCommGrpCat.of (ULift.{u} ℤ))) (i : I) :
    integralPathBasisDesc s (FreeAbelianGroup.of i) = s.inj i (ULift.up (1 : ℤ)) :=
  FreeAbelianGroup.lift_apply_of (fun j => s.inj j (ULift.up (1 : ℤ))) i

end CategoryTheory

namespace CategoryTheory

/-- The literal path-basis cofan satisfies the integral coproduct universal property. -/
noncomputable def integralPathBasisCofanIsColimit (I : Type u) :
    Limits.IsColimit (integralPathBasisCofan I) := by
  refine Limits.Cofan.IsColimit.mk (integralPathBasisCofan I)
    (fun s => integralPathBasisDesc s) ?_ ?_
  · intro s i
    apply (AddCommGrpCat.uliftZMultiplesAddEquiv s.pt).injective
    change integralPathBasisDesc s
        ((integralPathBasisCofan I).inj i (ULift.up (1 : ℤ))) =
      s.inj i (ULift.up (1 : ℤ))
    have hi : (integralPathBasisCofan I).inj i (ULift.up (1 : ℤ)) =
        FreeAbelianGroup.of i :=
      (integralPathBasisCofan_inj I i (ULift.up (1 : ℤ))).trans (one_zsmul _)
    exact (congrArg (fun a : FreeAbelianGroup I => integralPathBasisDesc s a) hi).trans
      (integralPathBasisDesc_of s i)
  · intro s m hm
    apply AddCommGrpCat.hom_ext
    refine FreeAbelianGroup.lift_ext m.hom (integralPathBasisDesc s).hom ?_
    intro i
    have hi : (integralPathBasisCofan I).inj i (ULift.up (1 : ℤ)) =
        FreeAbelianGroup.of i :=
      (integralPathBasisCofan_inj I i (ULift.up (1 : ℤ))).trans (one_zsmul _)
    have hv : m ((integralPathBasisCofan I).inj i (ULift.up (1 : ℤ))) =
        s.inj i (ULift.up (1 : ℤ)) :=
      congrArg (fun f : AddCommGrpCat.of (ULift.{u} ℤ) ⟶ s.pt =>
        f (ULift.up (1 : ℤ))) (hm i)
    exact (congrArg (fun a : FreeAbelianGroup I => m a) hi.symm).trans
      (hv.trans (integralPathBasisDesc_of s i).symm)

/-- Deprecated alias for `integralPathBasisCofanIsColimit`. -/
@[deprecated integralPathBasisCofanIsColimit (since := "2026-10-28"),
  nolint defsWithUnderscore]
alias integralPathBasisCofan_isColimit := integralPathBasisCofanIsColimit

/-- The canonical integral coproduct identifies with the actual free path-basis group. -/
noncomputable def integralPathBasisIso (I : Type u) :
    (∐ fun _ : I => AddCommGrpCat.of (ULift.{u} ℤ)) ≅
      AddCommGrpCat.of (FreeAbelianGroup I) :=
  (Limits.coproductIsCoproduct
    (fun _ : I => AddCommGrpCat.of (ULift.{u} ℤ))).coconePointUniqueUpToIso
    (integralPathBasisCofanIsColimit I)

end CategoryTheory


namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- The regular path basis with its canonical integral module and direct transports. -/
def regularPathModuleCoefficientFunctor (y : C) : C ⥤ ModuleCat.{v} ℤ where
  obj z := ModuleCat.of ℤ (FreeAbelianGroup (y ⟶ z))
  map f := ModuleCat.ofHom (regularPathCoefficientTransport y f).toIntLinearMap
  map_id z := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact congrArg
      (fun h : FreeAbelianGroup (y ⟶ z) →+ FreeAbelianGroup (y ⟶ z) => h a)
      (regularPathCoefficientTransport_id y z)
  map_comp {a b c} f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro t
    exact congrArg
      (fun h : FreeAbelianGroup (y ⟶ a) →+ FreeAbelianGroup (y ⟶ c) => h t)
      (regularPathCoefficientTransport_comp y f g)

/-- Forgetting the canonical integral structure keeps the actual path coefficient functor. -/
theorem regularPathModuleCoefficientFunctor_forget (y : C) :
    regularPathModuleCoefficientFunctor y ⋙
        forget₂ (ModuleCat.{v} ℤ) AddCommGrpCat.{v} =
      regularPathCoefficientFunctor y := by
  rfl

/-- The integral-module transport retains the original forward path on each basis element. -/
theorem regularPathModuleCoefficientFunctor_map_of (y : C) {z z' : C}
    (f : z ⟶ z') (γ : y ⟶ z) :
    (regularPathModuleCoefficientFunctor y).map f (FreeAbelianGroup.of γ) =
      FreeAbelianGroup.of (γ ≫ f) := by
  change regularPathCoefficientTransport y f (FreeAbelianGroup.of γ) = _
  exact regularPathCoefficientTransport_of y f γ

end CategoryTheory


namespace CategoryTheory

/-- The canonical integral module comparison uses the actual forgetful equivalence. -/
noncomputable def integralPathModuleBasisIso (I : Type u) :
    (∐ fun _ : I => ModuleCat.of ℤ (ULift.{u} ℤ)) ≅
      ModuleCat.of ℤ (FreeAbelianGroup I) :=
  (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).preimageIso
    (Limits.PreservesCoproduct.iso
      (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u})
      (fun _ : I => ModuleCat.of ℤ (ULift.{u} ℤ)) ≪≫ integralPathBasisIso I)

/-- Forgetting its forward map gives the actual coproduct comparison and path-basis map. -/
theorem integralPathModuleBasisIso_map_hom (I : Type u) :
    (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).map
        (integralPathModuleBasisIso I).hom =
      (Limits.PreservesCoproduct.iso
        (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u})
        (fun _ : I => ModuleCat.of ℤ (ULift.{u} ℤ))).hom ≫
          (integralPathBasisIso I).hom := by
  change (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).map
      ((forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).preimage _) = _
  exact (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).map_preimage _

end CategoryTheory


namespace CategoryTheory

/-- The module basis sends each original integral summand along its canonical basis leg. -/
theorem integralPathModuleBasisIso_hom_ι (I : Type u) (i : I) :
    Limits.Sigma.ι (fun _ : I => ModuleCat.of ℤ (ULift.{u} ℤ)) i ≫
        (integralPathModuleBasisIso I).hom =
      ModuleCat.ofHom
        (uliftZMultiplesHom (FreeAbelianGroup I) (FreeAbelianGroup.of i)).toIntLinearMap := by
  let U : ModuleCat.{u} ℤ ⥤ AddCommGrpCat.{u} :=
    forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}
  let P := Limits.PreservesCoproduct.iso U
    (fun _ : I => ModuleCat.of ℤ (ULift.{u} ℤ))
  have hU : U.map (Limits.Sigma.ι (fun _ : I => ModuleCat.of ℤ (ULift.{u} ℤ)) i) ≫
        P.hom =
      Limits.Sigma.ι (fun _ : I => AddCommGrpCat.of (ULift.{u} ℤ)) i := by
    apply (cancel_mono P.inv).1
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    simpa only [U, P, ModuleCat.forget₂_obj_moduleCat_of,
      Limits.PreservesCoproduct.inv_hom] using
      (Limits.ι_comp_sigmaComparison U
        (fun _ : I => ModuleCat.of ℤ (ULift.{u} ℤ)) i).symm
  apply U.map_injective
  rw [Functor.map_comp, integralPathModuleBasisIso_map_hom]
  rw [← Category.assoc, hU]
  change Limits.Sigma.ι (fun _ : I => AddCommGrpCat.of (ULift.{u} ℤ)) i ≫
      (integralPathBasisIso I).hom = (integralPathBasisCofan I).inj i
  exact Limits.IsColimit.comp_coconePointUniqueUpToIso_hom
    (Limits.coproductIsCoproduct (fun _ : I => AddCommGrpCat.of (ULift.{u} ℤ)))
    (integralPathBasisCofanIsColimit I) (Discrete.mk i)

/-- The forward module basis preserves every integral coefficient. -/
theorem integralPathModuleBasisIso_hom_ι_apply (I : Type u) (i : I) (z : ULift.{u} ℤ) :
    (integralPathModuleBasisIso I).hom
        (Limits.Sigma.ι (fun _ : I => ModuleCat.of ℤ (ULift.{u} ℤ)) i z) =
      z.down • FreeAbelianGroup.of i := by
  have h := congrArg
    (fun f : ModuleCat.of ℤ (ULift.{u} ℤ) ⟶ ModuleCat.of ℤ (FreeAbelianGroup I) => f z)
    (integralPathModuleBasisIso_hom_ι I i)
  exact h.trans
    (uliftZMultiplesHom_apply_apply (FreeAbelianGroup I) (FreeAbelianGroup.of i) z)

/-- The inverse module basis returns the original unit inclusion of a path. -/
theorem integralPathModuleBasisIso_inv_of (I : Type u) (i : I) :
    (integralPathModuleBasisIso I).inv (FreeAbelianGroup.of i) =
      Limits.Sigma.ι (fun _ : I => ModuleCat.of ℤ (ULift.{u} ℤ)) i (ULift.up (1 : ℤ)) := by
  have h : (integralPathModuleBasisIso I).hom
        (Limits.Sigma.ι (fun _ : I => ModuleCat.of ℤ (ULift.{u} ℤ)) i (ULift.up (1 : ℤ))) =
      FreeAbelianGroup.of i :=
    (integralPathModuleBasisIso_hom_ι_apply I i (ULift.up (1 : ℤ))).trans (one_zsmul _)
  have hi : (integralPathModuleBasisIso I).inv
        ((integralPathModuleBasisIso I).hom
          (Limits.Sigma.ι (fun _ : I => ModuleCat.of ℤ (ULift.{u} ℤ)) i
            (ULift.up (1 : ℤ)))) =
      Limits.Sigma.ι (fun _ : I => ModuleCat.of ℤ (ULift.{u} ℤ)) i (ULift.up (1 : ℤ)) :=
    congrArg (fun f : (∐ fun _ : I => ModuleCat.of ℤ (ULift.{u} ℤ)) ⟶
      (∐ fun _ : I => ModuleCat.of ℤ (ULift.{u} ℤ)) =>
      f (Limits.Sigma.ι (fun _ : I => ModuleCat.of ℤ (ULift.{u} ℤ)) i
        (ULift.up (1 : ℤ)))) (integralPathModuleBasisIso I).hom_inv_id
  exact (congrArg (fun a : FreeAbelianGroup I => (integralPathModuleBasisIso I).inv a)
    h.symm).trans hi

/-- The inverse module basis preserves all integer weights on original path generators. -/
theorem integralPathModuleBasisIso_inv_zsmul (I : Type u) (i : I) (z : ℤ) :
    (integralPathModuleBasisIso I).inv (z • FreeAbelianGroup.of i) =
      Limits.Sigma.ι (fun _ : I => ModuleCat.of ℤ (ULift.{u} ℤ)) i (ULift.up z) := by
  have h := integralPathModuleBasisIso_hom_ι_apply I i (ULift.up z)
  have hi : (integralPathModuleBasisIso I).inv
        ((integralPathModuleBasisIso I).hom
          (Limits.Sigma.ι (fun _ : I => ModuleCat.of ℤ (ULift.{u} ℤ)) i (ULift.up z))) =
      Limits.Sigma.ι (fun _ : I => ModuleCat.of ℤ (ULift.{u} ℤ)) i (ULift.up z) :=
    congrArg (fun f : (∐ fun _ : I => ModuleCat.of ℤ (ULift.{u} ℤ)) ⟶
      (∐ fun _ : I => ModuleCat.of ℤ (ULift.{u} ℤ)) =>
      f (Limits.Sigma.ι (fun _ : I => ModuleCat.of ℤ (ULift.{u} ℤ)) i
        (ULift.up z))) (integralPathModuleBasisIso I).hom_inv_id
  exact (congrArg (fun a : FreeAbelianGroup I => (integralPathModuleBasisIso I).inv a)
    h.symm).trans hi

end CategoryTheory

open scoped Simplicial

namespace SSet.KanComplex

/-- The original local coefficient endpoint is computed from its actual unit simplex. -/
theorem regularLocalCoefficientFirstObject_eq
    {X : SSet.{u}} {n : ℕ} (s : X _⦋n⦌) :
    let σ : (Δ[n] : SSet.{u}) ⟶ X := SSet.yonedaEquiv.symm s
    let α : (Δ[0] : SSet.{u}) ⟶ Δ[n] := SSet.yonedaEquiv.symm
      (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1)))
    ComposableArrows.left
        ((SSet.fundamentalGroupoidNerveUnit X).app (Opposite.op ⦋n⦌) s) =
      SSet.FundamentalGroupoid.mk ((SSet.yonedaEquiv (n := ⦋0⦌)) (α ≫ σ)) := by
  let Γ : Type u := SSet.FundamentalGroupoid X
  let σ : (Δ[n] : SSet.{u}) ⟶ X := SSet.yonedaEquiv.symm s
  have hσ : (SSet.yonedaEquiv (X := X) (n := ⦋n⦌)) σ = s :=
    (SSet.yonedaEquiv (X := X) (n := ⦋n⦌)).apply_symm_apply s
  have hu : SSet.yonedaEquiv (σ ≫ nativeCoverUnit X) =
      (SSet.fundamentalGroupoidNerveUnit X).app (Opposite.op ⦋n⦌) s :=
    (SSet.yonedaEquiv_comp σ (nativeCoverUnit X)).trans
      (congrArg (fun t : X _⦋n⦌ => (nativeCoverUnit X).app (Opposite.op ⦋n⦌) t) hσ)
  exact (congrArg (fun T : ComposableArrows Γ n => T.obj (0 : Fin (n + 1))) hu).symm.trans
    (nativeCoverUnitChain_firstVertex_eq σ)

/-- The independent path-basis indices retain the original simplex and coefficient functor. -/
def regularLocalCoefficientPathGenerators
    {X : SSet.{u}} {C : Type v} [Category.{u} C]
    (F : SSet.FundamentalGroupoid X ⥤ C) (y : C) (n : ℕ) : Type u :=
  Σ σ : (Δ[n] : SSet.{u}) ⟶ X, y ⟶ F.obj
    (SSet.FundamentalGroupoid.mk
      ((SSet.yonedaEquiv (n := ⦋0⦌))
        ((SSet.yonedaEquiv.symm (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1))) :
          (Δ[0] : SSet.{u}) ⟶ Δ[n]) ≫ σ)))

/-- Reindex the actual coefficient paths by Yoneda and their derived endpoint equality. -/
noncomputable def regularLocalCoefficientPathIndexEquiv
    {X : SSet.{u}} {C : Type v} [Category.{u} C]
    (F : SSet.FundamentalGroupoid X ⥤ C) (y : C) (n : ℕ) :
    (Σ s : X _⦋n⦌, y ⟶ F.obj (ComposableArrows.left
      ((SSet.fundamentalGroupoidNerveUnit X).app (Opposite.op ⦋n⦌) s))) ≃
      regularLocalCoefficientPathGenerators F y n :=
  Equiv.sigmaCongr (SSet.yonedaEquiv (X := X) (n := ⦋n⦌)).symm
    (fun s => Iso.homCongr (Iso.refl y)
      (eqToIso (congrArg F.obj (regularLocalCoefficientFirstObject_eq s))))

/-- The original path is postcomposed with the actual mapped endpoint transport. -/
theorem regularLocalCoefficientPathIndexEquiv_apply
    {X : SSet.{u}} {C : Type v} [Category.{u} C]
    (F : SSet.FundamentalGroupoid X ⥤ C) (y : C) (n : ℕ) (s : X _⦋n⦌)
    (γ : y ⟶ F.obj (ComposableArrows.left
      ((SSet.fundamentalGroupoidNerveUnit X).app (Opposite.op ⦋n⦌) s))) :
    regularLocalCoefficientPathIndexEquiv F y n ⟨s, γ⟩ =
      ⟨SSet.yonedaEquiv.symm s,
        γ ≫ eqToHom (congrArg F.obj (regularLocalCoefficientFirstObject_eq s))⟩ := by
  let σ : (Δ[n] : SSet.{u}) ⟶ X := SSet.yonedaEquiv.symm s
  let κ := congrArg F.obj (regularLocalCoefficientFirstObject_eq s)
  change (⟨σ, 𝟙 _ ≫ (γ ≫ eqToHom κ)⟩ :
    regularLocalCoefficientPathGenerators F y n) = ⟨σ, γ ≫ eqToHom κ⟩
  exact congrArg (fun δ : y ⟶ F.obj (SSet.FundamentalGroupoid.mk
      ((SSet.yonedaEquiv (n := ⦋0⦌))
        ((SSet.yonedaEquiv.symm (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1))) :
          (Δ[0] : SSet.{u}) ⟶ Δ[n]) ≫ σ))) =>
    (⟨σ, δ⟩ : regularLocalCoefficientPathGenerators F y n))
    (Category.id_comp (γ ≫ eqToHom κ))

/-- Flatten the constructed integral basis of the existing original coefficient object. -/
noncomputable def regularLocalCoefficientIntegralBasisIso
    {X : SSet.{u}} {C : Type v} [Category.{u} C]
    (F : SSet.FundamentalGroupoid X ⥤ C) (y : C) (n : ℕ) :
    SSet.localCoefficientObj (F ⋙ CategoryTheory.regularPathModuleCoefficientFunctor y) n ≅
      ∐ fun _ : regularLocalCoefficientPathGenerators F y n =>
        ModuleCat.of ℤ (ULift.{u} ℤ) := by
  let H : X _⦋n⦌ → Type u := fun s => y ⟶ F.obj (ComposableArrows.left
    ((SSet.fundamentalGroupoidNerveUnit X).app (Opposite.op ⦋n⦌) s))
  let Z : ModuleCat.{u} ℤ := ModuleCat.of ℤ (ULift.{u} ℤ)
  change (∐ fun s : X _⦋n⦌ => ModuleCat.of ℤ (FreeAbelianGroup (H s))) ≅
    ∐ fun _ : regularLocalCoefficientPathGenerators F y n => Z
  exact (Limits.Sigma.mapIso (fun s : X _⦋n⦌ =>
      (CategoryTheory.integralPathModuleBasisIso (H s)).symm)) ≪≫
    (Limits.sigmaSigmaIso H (fun s (_ : H s) => Z)) ≪≫
    (Limits.Sigma.whiskerEquiv (regularLocalCoefficientPathIndexEquiv F y n)
      (fun _ => Iso.refl Z))

end SSet.KanComplex


namespace SSet.KanComplex

/-- The original degree comparison preserves every integer on each original path summand. -/
theorem regularLocalCoefficientIntegralBasisIso_hom_ι_basis
    {X : SSet.{u}} {C : Type v} [Category.{u} C]
    (F : SSet.FundamentalGroupoid X ⥤ C) (y : C) (n : ℕ)
    (s : X _⦋n⦌)
    (γ : y ⟶ F.obj (ComposableArrows.left
      ((SSet.fundamentalGroupoidNerveUnit X).app (Opposite.op ⦋n⦌) s)))
    (z : ℤ) :
    (regularLocalCoefficientIntegralBasisIso F y n).hom
        (CategoryTheory.CategoryHomology.nervePullbackCoefficientι
          (SSet.fundamentalGroupoidNerveUnit X)
          (F ⋙ CategoryTheory.regularPathModuleCoefficientFunctor y) s
          (z • FreeAbelianGroup.of γ)) =
      Limits.Sigma.ι (fun _ : regularLocalCoefficientPathGenerators F y n =>
        ModuleCat.of ℤ (ULift.{u} ℤ))
        ⟨SSet.yonedaEquiv.symm s,
          γ ≫ eqToHom (congrArg F.obj (regularLocalCoefficientFirstObject_eq s))⟩
        (ULift.up z) := by
  let H : X _⦋n⦌ → Type u := fun t => y ⟶ F.obj (ComposableArrows.left
    ((SSet.fundamentalGroupoidNerveUnit X).app (Opposite.op ⦋n⦌) t))
  let Z : ModuleCat.{u} ℤ := ModuleCat.of ℤ (ULift.{u} ℤ)
  let A := Limits.Sigma.mapIso (fun t : X _⦋n⦌ =>
    (CategoryTheory.integralPathModuleBasisIso (H t)).symm)
  let B := Limits.sigmaSigmaIso H (fun t (_ : H t) => Z)
  let E := regularLocalCoefficientPathIndexEquiv F y n
  let Q := Limits.Sigma.whiskerEquiv
    (f := fun _ : (Σ t : X _⦋n⦌, H t) => Z)
    (g := fun _ : regularLocalCoefficientPathGenerators F y n => Z)
    E (fun _ => Iso.refl Z)
  have hA : A.hom
        (Limits.Sigma.ι (fun t : X _⦋n⦌ => ModuleCat.of ℤ (FreeAbelianGroup (H t))) s
          (z • FreeAbelianGroup.of γ)) =
      Limits.Sigma.ι (fun t : X _⦋n⦌ => ∐ fun _ : H t => Z) s
        (Limits.Sigma.ι (fun _ : H s => Z) γ (ULift.up z)) := by
    have hm := Limits.Sigma.ι_mapIso_hom (fun t : X _⦋n⦌ =>
      (CategoryTheory.integralPathModuleBasisIso (H t)).symm) s
    have hv := congrArg
      (fun g : ModuleCat.of ℤ (FreeAbelianGroup (H s)) ⟶
        (∐ fun t : X _⦋n⦌ => ∐ fun _ : H t => Z) => g (z • FreeAbelianGroup.of γ)) hm
    change A.hom
        (Limits.Sigma.ι (fun t : X _⦋n⦌ => ModuleCat.of ℤ (FreeAbelianGroup (H t))) s
          (z • FreeAbelianGroup.of γ)) =
      Limits.Sigma.ι (fun t : X _⦋n⦌ => ∐ fun _ : H t => Z) s
        ((CategoryTheory.integralPathModuleBasisIso (H s)).inv
          (z • FreeAbelianGroup.of γ)) at hv
    exact hv.trans (congrArg
      (fun a : ((∐ fun _ : H s => Z) : ModuleCat.{u} ℤ) =>
        Limits.Sigma.ι (fun t : X _⦋n⦌ => ∐ fun _ : H t => Z) s a)
      (CategoryTheory.integralPathModuleBasisIso_inv_zsmul (H s) γ z))
  have hBm : Limits.Sigma.ι (fun _ : H s => Z) γ ≫
        Limits.Sigma.ι (fun t : X _⦋n⦌ => ∐ fun _ : H t => Z) s ≫ B.hom =
      Limits.Sigma.ι (fun _ : (Σ t : X _⦋n⦌, H t) => Z) ⟨s, γ⟩ := by
    dsimp only [B]
    rw [Limits.sigmaSigmaIso_hom, Limits.Sigma.ι_comp_desc, Limits.Sigma.ι_comp_desc]
  have hB := congrArg
    (fun g : Z ⟶ (∐ fun _ : (Σ t : X _⦋n⦌, H t) => Z) => g (ULift.up z)) hBm
  have hQm : Limits.Sigma.ι (fun _ : (Σ t : X _⦋n⦌, H t) => Z) ⟨s, γ⟩ ≫
        Q.hom =
      Limits.Sigma.ι (fun _ : regularLocalCoefficientPathGenerators F y n => Z)
        (E ⟨s, γ⟩) := by
    dsimp only [Q]
    rw [Limits.Sigma.whiskerEquiv_hom, Limits.Sigma.ι_comp_map']
    exact Category.id_comp _
  have hQ := congrArg
    (fun g : Z ⟶ (∐ fun _ : regularLocalCoefficientPathGenerators F y n => Z) =>
      g (ULift.up z)) hQm
  have he := regularLocalCoefficientPathIndexEquiv_apply F y n s γ
  change Q.hom (B.hom (A.hom
      (Limits.Sigma.ι (fun t : X _⦋n⦌ => ModuleCat.of ℤ (FreeAbelianGroup (H t))) s
        (z • FreeAbelianGroup.of γ)))) = _
  calc
    _ = Q.hom (B.hom
        (Limits.Sigma.ι (fun t : X _⦋n⦌ => ∐ fun _ : H t => Z) s
          (Limits.Sigma.ι (fun _ : H s => Z) γ (ULift.up z)))) :=
      congrArg (fun a => Q.hom (B.hom a)) hA
    _ = Q.hom
        (Limits.Sigma.ι (fun _ : (Σ t : X _⦋n⦌, H t) => Z) ⟨s, γ⟩ (ULift.up z)) :=
      congrArg Q.hom hB
    _ = Limits.Sigma.ι (fun _ : regularLocalCoefficientPathGenerators F y n => Z)
        (E ⟨s, γ⟩) (ULift.up z) := hQ
    _ = _ := congrArg
      (fun q : regularLocalCoefficientPathGenerators F y n =>
        Limits.Sigma.ι (fun _ : regularLocalCoefficientPathGenerators F y n => Z) q
          (ULift.up z)) he

/-- The inverse uses the computed original index preimage and preserves every integer. -/
theorem regularLocalCoefficientIntegralBasisIso_inv_ι_basis
    {X : SSet.{u}} {C : Type v} [Category.{u} C]
    (F : SSet.FundamentalGroupoid X ⥤ C) (y : C) (n : ℕ)
    (p : regularLocalCoefficientPathGenerators F y n) (z : ℤ) :
    let q := (regularLocalCoefficientPathIndexEquiv F y n).symm p
    (regularLocalCoefficientIntegralBasisIso F y n).inv
        (Limits.Sigma.ι (fun _ : regularLocalCoefficientPathGenerators F y n =>
          ModuleCat.of ℤ (ULift.{u} ℤ)) p (ULift.up z)) =
      CategoryTheory.CategoryHomology.nervePullbackCoefficientι
        (SSet.fundamentalGroupoidNerveUnit X)
        (F ⋙ CategoryTheory.regularPathModuleCoefficientFunctor y) q.1
        (z • FreeAbelianGroup.of q.2) := by
  let q := (regularLocalCoefficientPathIndexEquiv F y n).symm p
  have hq : regularLocalCoefficientPathIndexEquiv F y n q = p :=
    (regularLocalCoefficientPathIndexEquiv F y n).apply_symm_apply p
  have hj := (regularLocalCoefficientPathIndexEquiv_apply F y n q.1 q.2).symm.trans hq
  have hf := (regularLocalCoefficientIntegralBasisIso_hom_ι_basis F y n q.1 q.2 z).trans
    (congrArg (fun t : regularLocalCoefficientPathGenerators F y n =>
      Limits.Sigma.ι (fun _ : regularLocalCoefficientPathGenerators F y n =>
        ModuleCat.of ℤ (ULift.{u} ℤ)) t (ULift.up z)) hj)
  have hi : (regularLocalCoefficientIntegralBasisIso F y n).inv
        ((regularLocalCoefficientIntegralBasisIso F y n).hom
          (CategoryTheory.CategoryHomology.nervePullbackCoefficientι
            (SSet.fundamentalGroupoidNerveUnit X)
            (F ⋙ CategoryTheory.regularPathModuleCoefficientFunctor y) q.1
            (z • FreeAbelianGroup.of q.2))) =
      CategoryTheory.CategoryHomology.nervePullbackCoefficientι
        (SSet.fundamentalGroupoidNerveUnit X)
        (F ⋙ CategoryTheory.regularPathModuleCoefficientFunctor y) q.1
        (z • FreeAbelianGroup.of q.2) :=
    congrArg (fun g : SSet.localCoefficientObj
      (F ⋙ CategoryTheory.regularPathModuleCoefficientFunctor y) n ⟶
      SSet.localCoefficientObj (F ⋙ CategoryTheory.regularPathModuleCoefficientFunctor y) n =>
      g (CategoryTheory.CategoryHomology.nervePullbackCoefficientι
        (SSet.fundamentalGroupoidNerveUnit X)
        (F ⋙ CategoryTheory.regularPathModuleCoefficientFunctor y) q.1
        (z • FreeAbelianGroup.of q.2)))
      (regularLocalCoefficientIntegralBasisIso F y n).hom_inv_id
  exact (congrArg (fun a : ((∐ fun _ : regularLocalCoefficientPathGenerators F y n =>
    ModuleCat.of ℤ (ULift.{u} ℤ)) : ModuleCat.{u} ℤ) =>
    (regularLocalCoefficientIntegralBasisIso F y n).inv a) hf.symm).trans hi

end SSet.KanComplex


namespace SSet.KanComplex

/-- The original unit restriction and its endpoint casts give the actual native base transport. -/
theorem regularLocalCoefficientRestrictionTransport
    {X : SSet.{u}} {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) (s : X _⦋n⦌) :
    let Γ : Type u := SSet.FundamentalGroupoid X
    let η : X ⟶ CategoryTheory.nerve Γ := SSet.fundamentalGroupoidNerveUnit X
    let σ : (Δ[n] : SSet.{u}) ⟶ X := SSet.yonedaEquiv.symm s
    let t : X _⦋m⦌ := X.map θ.op s
    let τ : (Δ[m] : SSet.{u}) ⟶ X := SSet.yonedaEquiv.symm t
    let T : ComposableArrows Γ n := η.app (Opposite.op ⦋n⦌) s
    let S : ComposableArrows Γ m := η.app (Opposite.op ⦋m⦌) t
    let j : Fin (n + 1) := θ.toOrderHom (0 : Fin (m + 1))
    let ε : (CategoryTheory.nerve Γ).map θ.op T = S :=
      (ConcreteCategory.congr_hom (η.naturality θ.op) s).symm
    let μ : T.obj j = S.left := congrArg ComposableArrows.left ε
    let α : (Δ[0] : SSet.{u}) ⟶ Δ[m] := SSet.yonedaEquiv.symm
      (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin (m + 1)))
    let ν : SSet.FundamentalGroupoid.mk ((SSet.yonedaEquiv (n := ⦋0⦌)) (α ≫ τ)) =
        SSet.FundamentalGroupoid.mk
          ((SSet.yonedaEquiv (n := ⦋0⦌)) (α ≫ (SSet.stdSimplex.map θ ≫ σ))) :=
      congrArg (fun a : (Δ[m] : SSet.{u}) ⟶ X => SSet.FundamentalGroupoid.mk
        ((SSet.yonedaEquiv (n := ⦋0⦌)) (α ≫ a)))
        (SSet.yonedaEquiv_symm_naturality_left θ s).symm
    T.map (homOfLE (Fin.zero_le j)) ≫ eqToHom μ ≫
        eqToHom (regularLocalCoefficientFirstObject_eq t) ≫ eqToHom ν =
      eqToHom (regularLocalCoefficientFirstObject_eq s) ≫
        nativeCoverSimplexPathTransport σ θ := by
  let Γ : Type u := SSet.FundamentalGroupoid X
  let η : X ⟶ CategoryTheory.nerve Γ := SSet.fundamentalGroupoidNerveUnit X
  let σ : (Δ[n] : SSet.{u}) ⟶ X := SSet.yonedaEquiv.symm s
  let t : X _⦋m⦌ := X.map θ.op s
  let τ : (Δ[m] : SSet.{u}) ⟶ X := SSet.yonedaEquiv.symm t
  let T : ComposableArrows Γ n := η.app (Opposite.op ⦋n⦌) s
  let S : ComposableArrows Γ m := η.app (Opposite.op ⦋m⦌) t
  let j : Fin (n + 1) := θ.toOrderHom (0 : Fin (m + 1))
  let ε : (CategoryTheory.nerve Γ).map θ.op T = S :=
    (ConcreteCategory.congr_hom (η.naturality θ.op) s).symm
  let μ : T.obj j = S.left := congrArg ComposableArrows.left ε
  let α : (Δ[0] : SSet.{u}) ⟶ Δ[m] := SSet.yonedaEquiv.symm
    (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin (m + 1)))
  let ν : SSet.FundamentalGroupoid.mk ((SSet.yonedaEquiv (n := ⦋0⦌)) (α ≫ τ)) =
      SSet.FundamentalGroupoid.mk
        ((SSet.yonedaEquiv (n := ⦋0⦌)) (α ≫ (SSet.stdSimplex.map θ ≫ σ))) :=
    congrArg (fun a : (Δ[m] : SSet.{u}) ⟶ X => SSet.FundamentalGroupoid.mk
      ((SSet.yonedaEquiv (n := ⦋0⦌)) (α ≫ a)))
      (SSet.yonedaEquiv_symm_naturality_left θ s).symm
  let V : ComposableArrows Γ n := SSet.yonedaEquiv (σ ≫ nativeCoverUnit X)
  have hV : V = T :=
    (SSet.yonedaEquiv_comp σ (nativeCoverUnit X)).trans
      (congrArg (fun a : X _⦋n⦌ => (nativeCoverUnit X).app (Opposite.op ⦋n⦌) a)
        ((SSet.yonedaEquiv (X := X) (n := ⦋n⦌)).apply_symm_apply s))
  let κ := regularLocalCoefficientFirstObject_eq s
  let κ' := regularLocalCoefficientFirstObject_eq t
  let κV := nativeCoverUnitChain_firstVertex_eq σ
  let κR := nativeCoverUnitChain_restrictedFirst_eq σ θ
  have h0 : κ.trans κV.symm =
      congrArg (fun A : ComposableArrows Γ n => A.obj (0 : Fin (n + 1))) hV.symm :=
    Subsingleton.elim _ _
  have hj : (congrArg (fun A : ComposableArrows Γ n => A.obj j) hV.symm).trans κR =
      (μ.trans κ').trans ν :=
    Subsingleton.elim _ _
  have hnat := CategoryTheory.eqToHom_naturality
    (f := fun A : ComposableArrows Γ n => A.obj (0 : Fin (n + 1)))
    (g := fun A : ComposableArrows Γ n => A.obj j)
    (fun A : ComposableArrows Γ n => A.map (homOfLE (Fin.zero_le j))) hV.symm
  change T.map (homOfLE (Fin.zero_le j)) ≫
      eqToHom (congrArg (fun A : ComposableArrows Γ n => A.obj j) hV.symm) =
    eqToHom (congrArg (fun A : ComposableArrows Γ n => A.obj (0 : Fin (n + 1))) hV.symm) ≫
      V.map (homOfLE (Fin.zero_le j)) at hnat
  change T.map (homOfLE (Fin.zero_le j)) ≫ eqToHom μ ≫ eqToHom κ' ≫ eqToHom ν =
    eqToHom κ ≫ nativeCoverSimplexPathTransport σ θ
  let Z : Γ := SSet.FundamentalGroupoid.mk
    ((SSet.yonedaEquiv (n := ⦋0⦌)) (α ≫ (SSet.stdSimplex.map θ ≫ σ)))
  let a0 : T.obj (0 : Fin (n + 1)) = V.obj (0 : Fin (n + 1)) :=
    congrArg (fun A : ComposableArrows Γ n => A.obj (0 : Fin (n + 1))) hV.symm
  let aj : T.obj j = V.obj j :=
    congrArg (fun A : ComposableArrows Γ n => A.obj j) hV.symm
  have hc0 : eqToHom (κ.trans κV.symm) = eqToHom a0 :=
    congrArg (fun e : T.obj (0 : Fin (n + 1)) = V.obj (0 : Fin (n + 1)) =>
      eqToHom e) h0
  have hcj : eqToHom ((μ.trans κ').trans ν) = eqToHom (aj.trans κR) :=
    congrArg (fun e : T.obj j = Z => eqToHom e) hj.symm
  have hr0 : eqToHom κ ≫ nativeCoverSimplexPathTransport σ θ =
      eqToHom (κ.trans κV.symm) ≫ V.map (homOfLE (Fin.zero_le j)) ≫ eqToHom κR := by
    change eqToHom κ ≫ (eqToHom κV.symm ≫
      V.map (homOfLE (Fin.zero_le j)) ≫ eqToHom κR) = _
    exact eqToHom_trans_assoc κ κV.symm
      (V.map (homOfLE (Fin.zero_le j)) ≫ eqToHom κR)
  have hr1 : eqToHom (κ.trans κV.symm) ≫
        V.map (homOfLE (Fin.zero_le j)) ≫ eqToHom κR =
      eqToHom a0 ≫ V.map (homOfLE (Fin.zero_le j)) ≫ eqToHom κR :=
    congrArg (fun f : T.obj (0 : Fin (n + 1)) ⟶ V.obj (0 : Fin (n + 1)) =>
      f ≫ V.map (homOfLE (Fin.zero_le j)) ≫ eqToHom κR) hc0
  have hr : eqToHom κ ≫ nativeCoverSimplexPathTransport σ θ =
      (eqToHom a0 ≫ V.map (homOfLE (Fin.zero_le j))) ≫ eqToHom κR :=
    hr0.trans (hr1.trans
      (Category.assoc (eqToHom a0) (V.map (homOfLE (Fin.zero_le j)))
        (eqToHom κR)).symm)
  have hl0 : T.map (homOfLE (Fin.zero_le j)) ≫
        eqToHom μ ≫ eqToHom κ' ≫ eqToHom ν =
      T.map (homOfLE (Fin.zero_le j)) ≫ eqToHom ((μ.trans κ').trans ν) :=
    congrArg (fun f : T.obj j ⟶ Z => T.map (homOfLE (Fin.zero_le j)) ≫ f)
      ((eqToHom_trans_assoc μ κ' (eqToHom ν)).trans (eqToHom_trans (μ.trans κ') ν))
  have hl1 : T.map (homOfLE (Fin.zero_le j)) ≫ eqToHom ((μ.trans κ').trans ν) =
      T.map (homOfLE (Fin.zero_le j)) ≫ eqToHom (aj.trans κR) :=
    congrArg (fun f : T.obj j ⟶ Z => T.map (homOfLE (Fin.zero_le j)) ≫ f) hcj
  have hl2 : T.map (homOfLE (Fin.zero_le j)) ≫ eqToHom (aj.trans κR) =
      T.map (homOfLE (Fin.zero_le j)) ≫ eqToHom aj ≫ eqToHom κR :=
    congrArg (fun f : T.obj j ⟶ Z => T.map (homOfLE (Fin.zero_le j)) ≫ f)
      (eqToHom_trans aj κR).symm
  have hl : T.map (homOfLE (Fin.zero_le j)) ≫
        eqToHom μ ≫ eqToHom κ' ≫ eqToHom ν =
      (T.map (homOfLE (Fin.zero_le j)) ≫ eqToHom aj) ≫ eqToHom κR :=
    hl0.trans (hl1.trans (hl2.trans
      (Category.assoc (T.map (homOfLE (Fin.zero_le j))) (eqToHom aj) (eqToHom κR)).symm))
  have hp : (T.map (homOfLE (Fin.zero_le j)) ≫ eqToHom aj) ≫ eqToHom κR =
      (eqToHom a0 ≫ V.map (homOfLE (Fin.zero_le j))) ≫ eqToHom κR :=
    congrArg (fun f : T.obj (0 : Fin (n + 1)) ⟶ V.obj j => f ≫ eqToHom κR) hnat
  exact hl.trans (hp.trans hr.symm)

end SSet.KanComplex


namespace SSet.KanComplex

/-- Original coefficient paths restrict using the actual unit arrow and its naturality cast. -/
def regularLocalCoefficientOriginalPathRestriction
    {X : SSet.{u}} {C : Type v} [Category.{u} C]
    (F : SSet.FundamentalGroupoid X ⥤ C) (y : C)
    {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    (Σ s : X _⦋n⦌, y ⟶ F.obj (ComposableArrows.left
      ((SSet.fundamentalGroupoidNerveUnit X).app (Opposite.op ⦋n⦌) s))) →
    (Σ t : X _⦋m⦌, y ⟶ F.obj (ComposableArrows.left
      ((SSet.fundamentalGroupoidNerveUnit X).app (Opposite.op ⦋m⦌) t))) :=
  fun a =>
    let Γ : Type u := SSet.FundamentalGroupoid X
    let η : X ⟶ CategoryTheory.nerve Γ := SSet.fundamentalGroupoidNerveUnit X
    let T : ComposableArrows Γ n := η.app (Opposite.op ⦋n⦌) a.1
    let t : X _⦋m⦌ := X.map θ.op a.1
    let S : ComposableArrows Γ m := η.app (Opposite.op ⦋m⦌) t
    let j : Fin (n + 1) := θ.toOrderHom (0 : Fin (m + 1))
    let ε : (CategoryTheory.nerve Γ).map θ.op T = S :=
      (ConcreteCategory.congr_hom (η.naturality θ.op) a.1).symm
    let μ : T.obj j = S.left := congrArg ComposableArrows.left ε
    ⟨t, a.2 ≫ F.map (T.map (homOfLE (Fin.zero_le j)) ≫ eqToHom μ)⟩

/-- Independent target pairs restrict their simplex and postcompose with the native base path. -/
def regularLocalCoefficientPathRestriction
    {X : SSet.{u}} {C : Type v} [Category.{u} C]
    (F : SSet.FundamentalGroupoid X ⥤ C) (y : C)
    {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    regularLocalCoefficientPathGenerators F y n →
      regularLocalCoefficientPathGenerators F y m :=
  fun a => ⟨SSet.stdSimplex.map θ ≫ a.1,
    a.2 ≫ F.map (nativeCoverSimplexPathTransport a.1 θ)⟩

/-- Every original coefficient path retains its endpoint transport under the mapped restriction. -/
theorem regularLocalCoefficientRestrictionTransport_map
    {X : SSet.{u}} {C : Type v} [Category.{u} C]
    (F : SSet.FundamentalGroupoid X ⥤ C) (y : C)
    {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) (s : X _⦋n⦌)
    (γ : y ⟶ F.obj (ComposableArrows.left
      ((SSet.fundamentalGroupoidNerveUnit X).app (Opposite.op ⦋n⦌) s))) :
    let σ : (Δ[n] : SSet.{u}) ⟶ X := SSet.yonedaEquiv.symm s
    let t : X _⦋m⦌ := X.map θ.op s
    let τ : (Δ[m] : SSet.{u}) ⟶ X := SSet.yonedaEquiv.symm t
    let α : (Δ[0] : SSet.{u}) ⟶ Δ[m] := SSet.yonedaEquiv.symm
      (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin (m + 1)))
    let ν : SSet.FundamentalGroupoid.mk ((SSet.yonedaEquiv (n := ⦋0⦌)) (α ≫ τ)) =
        SSet.FundamentalGroupoid.mk
          ((SSet.yonedaEquiv (n := ⦋0⦌)) (α ≫ (SSet.stdSimplex.map θ ≫ σ))) :=
      congrArg (fun a : (Δ[m] : SSet.{u}) ⟶ X => SSet.FundamentalGroupoid.mk
        ((SSet.yonedaEquiv (n := ⦋0⦌)) (α ≫ a)))
        (SSet.yonedaEquiv_symm_naturality_left θ s).symm
    (regularLocalCoefficientOriginalPathRestriction F y θ ⟨s, γ⟩).2 ≫
        eqToHom (congrArg F.obj (regularLocalCoefficientFirstObject_eq t)) ≫
        eqToHom (congrArg F.obj ν) =
      γ ≫ eqToHom (congrArg F.obj (regularLocalCoefficientFirstObject_eq s)) ≫
        F.map (nativeCoverSimplexPathTransport σ θ) := by
  let Γ : Type u := SSet.FundamentalGroupoid X
  let η : X ⟶ CategoryTheory.nerve Γ := SSet.fundamentalGroupoidNerveUnit X
  let σ : (Δ[n] : SSet.{u}) ⟶ X := SSet.yonedaEquiv.symm s
  let t : X _⦋m⦌ := X.map θ.op s
  let τ : (Δ[m] : SSet.{u}) ⟶ X := SSet.yonedaEquiv.symm t
  let T : ComposableArrows Γ n := η.app (Opposite.op ⦋n⦌) s
  let S : ComposableArrows Γ m := η.app (Opposite.op ⦋m⦌) t
  let j : Fin (n + 1) := θ.toOrderHom (0 : Fin (m + 1))
  let ε : (CategoryTheory.nerve Γ).map θ.op T = S :=
    (ConcreteCategory.congr_hom (η.naturality θ.op) s).symm
  let μ : T.obj j = S.left := congrArg ComposableArrows.left ε
  let α : (Δ[0] : SSet.{u}) ⟶ Δ[m] := SSet.yonedaEquiv.symm
    (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin (m + 1)))
  let ν : SSet.FundamentalGroupoid.mk ((SSet.yonedaEquiv (n := ⦋0⦌)) (α ≫ τ)) =
      SSet.FundamentalGroupoid.mk
        ((SSet.yonedaEquiv (n := ⦋0⦌)) (α ≫ (SSet.stdSimplex.map θ ≫ σ))) :=
    congrArg (fun a : (Δ[m] : SSet.{u}) ⟶ X => SSet.FundamentalGroupoid.mk
      ((SSet.yonedaEquiv (n := ⦋0⦌)) (α ≫ a)))
      (SSet.yonedaEquiv_symm_naturality_left θ s).symm
  let Z : Γ := SSet.FundamentalGroupoid.mk
    ((SSet.yonedaEquiv (n := ⦋0⦌)) (α ≫ (SSet.stdSimplex.map θ ≫ σ)))
  have hg := regularLocalCoefficientRestrictionTransport θ s
  change T.map (homOfLE (Fin.zero_le j)) ≫ eqToHom μ ≫
      eqToHom (regularLocalCoefficientFirstObject_eq t) ≫ eqToHom ν =
    eqToHom (regularLocalCoefficientFirstObject_eq s) ≫
      nativeCoverSimplexPathTransport σ θ at hg
  let αn : (Δ[0] : SSet.{u}) ⟶ Δ[n] := SSet.yonedaEquiv.symm
    (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1)))
  let N : Γ := SSet.FundamentalGroupoid.mk
    ((SSet.yonedaEquiv (n := ⦋0⦌)) (αn ≫ σ))
  let R : Γ := SSet.FundamentalGroupoid.mk
    ((SSet.yonedaEquiv (n := ⦋0⦌)) (α ≫ τ))
  let κ : T.left = N := regularLocalCoefficientFirstObject_eq s
  let κ' : S.left = R := regularLocalCoefficientFirstObject_eq t
  let q : T.left ⟶ S.left := T.map (homOfLE (Fin.zero_le j)) ≫ eqToHom μ
  let b : N ⟶ Z := nativeCoverSimplexPathTransport σ θ
  have hgq : q ≫ eqToHom κ' ≫ eqToHom ν = eqToHom κ ≫ b :=
    (Category.assoc (T.map (homOfLE (Fin.zero_le j))) (eqToHom μ)
      (eqToHom κ' ≫ eqToHom ν)).trans hg
  have hm : F.map (q ≫ eqToHom κ' ≫ eqToHom ν) = F.map (eqToHom κ ≫ b) :=
    congrArg (fun a : T.left ⟶ Z => F.map a) hgq
  have hl0 : F.map (q ≫ eqToHom κ' ≫ eqToHom ν) =
      F.map q ≫ F.map (eqToHom κ' ≫ eqToHom ν) :=
    F.map_comp q (eqToHom κ' ≫ eqToHom ν)
  have hl1 : F.map q ≫ F.map (eqToHom κ' ≫ eqToHom ν) =
      F.map q ≫ F.map (eqToHom κ') ≫ F.map (eqToHom ν) :=
    congrArg (fun f : F.obj S.left ⟶ F.obj Z => F.map q ≫ f)
      (F.map_comp (eqToHom κ') (eqToHom ν))
  have hc' : F.map (eqToHom κ') = eqToHom (congrArg F.obj κ') := eqToHom_map F κ'
  have hν : F.map (eqToHom ν) = eqToHom (congrArg F.obj ν) := eqToHom_map F ν
  have hl2 : F.map q ≫ F.map (eqToHom κ') ≫ F.map (eqToHom ν) =
      F.map q ≫ eqToHom (congrArg F.obj κ') ≫ F.map (eqToHom ν) :=
    congrArg (fun f : F.obj S.left ⟶ F.obj R => F.map q ≫ f ≫ F.map (eqToHom ν)) hc'
  have hl3 : F.map q ≫ eqToHom (congrArg F.obj κ') ≫ F.map (eqToHom ν) =
      F.map q ≫ eqToHom (congrArg F.obj κ') ≫ eqToHom (congrArg F.obj ν) :=
    congrArg (fun f : F.obj R ⟶ F.obj Z =>
      F.map q ≫ eqToHom (congrArg F.obj κ') ≫ f) hν
  have hl : F.map (q ≫ eqToHom κ' ≫ eqToHom ν) =
      F.map q ≫ eqToHom (congrArg F.obj κ') ≫ eqToHom (congrArg F.obj ν) :=
    hl0.trans (hl1.trans (hl2.trans hl3))
  have hr : F.map (eqToHom κ ≫ b) = eqToHom (congrArg F.obj κ) ≫ F.map b :=
    (F.map_comp (eqToHom κ) b).trans
      (congrArg (fun f : F.obj T.left ⟶ F.obj N => f ≫ F.map b) (eqToHom_map F κ))
  have hc : F.map q ≫ eqToHom (congrArg F.obj κ') ≫
        eqToHom (congrArg F.obj ν) = eqToHom (congrArg F.obj κ) ≫ F.map b :=
    hl.symm.trans (hm.trans hr)
  have hγ := congrArg (fun a : F.obj T.left ⟶ F.obj Z => γ ≫ a) hc
  change (γ ≫ F.map q) ≫ eqToHom (congrArg F.obj κ') ≫
    eqToHom (congrArg F.obj ν) = γ ≫ eqToHom (congrArg F.obj κ) ≫ F.map b
  exact (Category.assoc γ (F.map q)
    (eqToHom (congrArg F.obj κ') ≫ eqToHom (congrArg F.obj ν))).trans hγ

/-- The computed original index equivalence preserves every actual simplex restriction. -/
theorem regularLocalCoefficientPathIndexEquiv_restrict
    {X : SSet.{u}} {C : Type v} [Category.{u} C]
    (F : SSet.FundamentalGroupoid X ⥤ C) (y : C)
    {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) (s : X _⦋n⦌)
    (γ : y ⟶ F.obj (ComposableArrows.left
      ((SSet.fundamentalGroupoidNerveUnit X).app (Opposite.op ⦋n⦌) s))) :
    regularLocalCoefficientPathIndexEquiv F y m
        (regularLocalCoefficientOriginalPathRestriction F y θ ⟨s, γ⟩) =
      regularLocalCoefficientPathRestriction F y θ
        (regularLocalCoefficientPathIndexEquiv F y n ⟨s, γ⟩) := by
  let t : X _⦋m⦌ := X.map θ.op s
  let σ : (Δ[n] : SSet.{u}) ⟶ X := SSet.yonedaEquiv.symm s
  let τ : (Δ[m] : SSet.{u}) ⟶ X := SSet.yonedaEquiv.symm t
  let δ := (regularLocalCoefficientOriginalPathRestriction F y θ ⟨s, γ⟩).2
  let α : (Δ[0] : SSet.{u}) ⟶ Δ[m] := SSet.yonedaEquiv.symm
    (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin (m + 1)))
  let G : ((Δ[m] : SSet.{u}) ⟶ X) → C := fun a => F.obj
    (SSet.FundamentalGroupoid.mk ((SSet.yonedaEquiv (n := ⦋0⦌)) (α ≫ a)))
  let κ := congrArg F.obj (regularLocalCoefficientFirstObject_eq s)
  let κ' := congrArg F.obj (regularLocalCoefficientFirstObject_eq t)
  let γL : y ⟶ G τ := δ ≫ eqToHom κ'
  let γR : y ⟶ G (SSet.stdSimplex.map θ ≫ σ) :=
    γ ≫ eqToHom κ ≫ F.map (nativeCoverSimplexPathTransport σ θ)
  let ρ : τ = SSet.stdSimplex.map θ ≫ σ :=
    (SSet.yonedaEquiv_symm_naturality_left θ s).symm
  have hp : γL ≫ eqToHom (congrArg G ρ) = γR := by
    have h := regularLocalCoefficientRestrictionTransport_map F y θ s γ
    change δ ≫ eqToHom κ' ≫ eqToHom (congrArg G ρ) = γR at h
    change (δ ≫ eqToHom κ') ≫ eqToHom (congrArg G ρ) = γR
    exact (Category.assoc δ (eqToHom κ') (eqToHom (congrArg G ρ))).trans h
  have hl : regularLocalCoefficientPathIndexEquiv F y m
        (regularLocalCoefficientOriginalPathRestriction F y θ ⟨s, γ⟩) =
      (⟨τ, γL⟩ : regularLocalCoefficientPathGenerators F y m) := by
    change regularLocalCoefficientPathIndexEquiv F y m ⟨t, δ⟩ = _
    exact regularLocalCoefficientPathIndexEquiv_apply F y m t δ
  have hr : regularLocalCoefficientPathRestriction F y θ
        (regularLocalCoefficientPathIndexEquiv F y n ⟨s, γ⟩) =
      (⟨SSet.stdSimplex.map θ ≫ σ, γR⟩ : regularLocalCoefficientPathGenerators F y m) := by
    rw [regularLocalCoefficientPathIndexEquiv_apply]
    change (⟨SSet.stdSimplex.map θ ≫ σ,
      (γ ≫ eqToHom κ) ≫ F.map (nativeCoverSimplexPathTransport σ θ)⟩ :
      regularLocalCoefficientPathGenerators F y m) =
        ⟨SSet.stdSimplex.map θ ≫ σ, γR⟩
    exact congrArg (fun a : y ⟶ G (SSet.stdSimplex.map θ ≫ σ) =>
      (⟨SSet.stdSimplex.map θ ≫ σ, a⟩ : regularLocalCoefficientPathGenerators F y m))
      (Category.assoc γ (eqToHom κ) (F.map (nativeCoverSimplexPathTransport σ θ)))
  have hcast : ∀ (a b : (Δ[m] : SSet.{u}) ⟶ X) (e : a = b) (ξ : y ⟶ G a),
      (⟨b, ξ ≫ eqToHom (congrArg G e)⟩ : regularLocalCoefficientPathGenerators F y m) =
        ⟨a, ξ⟩ := by
    intro a b e ξ
    subst b
    change (⟨a, ξ ≫ 𝟙 (G a)⟩ : regularLocalCoefficientPathGenerators F y m) = ⟨a, ξ⟩
    exact congrArg (fun f : y ⟶ G a =>
      (⟨a, f⟩ : regularLocalCoefficientPathGenerators F y m)) (Category.comp_id ξ)
  have hpair : (⟨τ, γL⟩ : regularLocalCoefficientPathGenerators F y m) =
      ⟨SSet.stdSimplex.map θ ≫ σ, γR⟩ :=
    (hcast τ (SSet.stdSimplex.map θ ≫ σ) ρ γL).symm.trans
      (congrArg (fun a : y ⟶ G (SSet.stdSimplex.map θ ≫ σ) =>
        (⟨SSet.stdSimplex.map θ ≫ σ, a⟩ : regularLocalCoefficientPathGenerators F y m)) hp)
  exact hl.trans (hpair.trans hr.symm)

end SSet.KanComplex

namespace SSet.KanComplex

/-- Original source simplices paired with arbitrary-target-point native path coefficients. -/
def nativeCoverPullbackSimplexPathGenerators
    {X Y : SSet.{u}} (f : X ⟶ Y) (y : Y _⦋0⦌) (n : ℕ) : Type u :=
  Σ σ : (Δ[n] : SSet.{u}) ⟶ X,
    (SSet.FundamentalGroupoid.mk y ⟶ SSet.FundamentalGroupoid.mk
      ((SSet.yonedaEquiv (X := Y) (n := ⦋0⦌))
        ((SSet.yonedaEquiv.symm (SSet.stdSimplex.obj₀Equiv.symm
          (0 : Fin (n + 1))) : (Δ[0] : SSet.{u}) ⟶ Δ[n]) ≫ (σ ≫ f))))

/-- Actual pulled-back simplices arise from the original target-path coordinate inverse. -/
noncomputable def nativeCoverPullbackSimplexPathGeneratorsEquiv
    {X Y : SSet.{u}} (f : X ⟶ Y) (y : Y _⦋0⦌) (n : ℕ) :
    nativeCoverPullbackSimplexPathGenerators f y n ≃
      (pullback f (nativeCoverProjection Y y)) _⦋n⦌ :=
  (Equiv.sigmaCongrRight (fun σ : (Δ[n] : SSet.{u}) ⟶ X =>
      (nativeCoverPullbackSimplexPathEquiv f y σ).symm)).trans
    ((Equiv.sigmaFiberEquiv
        (fun L : (Δ[n] : SSet.{u}) ⟶ pullback f (nativeCoverProjection Y y) =>
          L ≫ pullback.fst f (nativeCoverProjection Y y))).trans
      (SSet.yonedaEquiv (X := pullback f (nativeCoverProjection Y y)) (n := ⦋n⦌)))

/-- The forward map uses the actual pullback lift, retaining the original target path. -/
theorem nativeCoverPullbackSimplexPathGeneratorsEquiv_apply
    {X Y : SSet.{u}} (f : X ⟶ Y) (y : Y _⦋0⦌) (n : ℕ)
    (g : nativeCoverPullbackSimplexPathGenerators f y n) :
    nativeCoverPullbackSimplexPathGeneratorsEquiv f y n g =
      (SSet.yonedaEquiv (X := pullback f (nativeCoverProjection Y y)) (n := ⦋n⦌))
        ((nativeCoverPullbackSimplexPathEquiv f y g.1).symm g.2).val := by
  rcases g with ⟨σ, γ⟩
  dsimp only [nativeCoverPullbackSimplexPathGeneratorsEquiv, Equiv.trans, Equiv.sigmaCongrRight,
    Equiv.sigmaFiberEquiv] ; rfl

/-- The inverse uses the original first projection and actual target-path comparison. -/
theorem nativeCoverPullbackSimplexPathGeneratorsEquiv_symm_apply
    {X Y : SSet.{u}} (f : X ⟶ Y) (y : Y _⦋0⦌) (n : ℕ)
    (s : (pullback f (nativeCoverProjection Y y)) _⦋n⦌) :
    (nativeCoverPullbackSimplexPathGeneratorsEquiv f y n).symm s =
      ⟨((SSet.yonedaEquiv (X := pullback f (nativeCoverProjection Y y)) (n := ⦋n⦌)).symm s) ≫
          pullback.fst f (nativeCoverProjection Y y),
        nativeCoverPullbackSimplexPathEquiv f y
          (((SSet.yonedaEquiv (X := pullback f (nativeCoverProjection Y y)) (n := ⦋n⦌)).symm s) ≫
            pullback.fst f (nativeCoverProjection Y y))
          ⟨(SSet.yonedaEquiv (X := pullback f (nativeCoverProjection Y y)) (n := ⦋n⦌)).symm s,
            rfl⟩⟩ := by
  dsimp only [nativeCoverPullbackSimplexPathGeneratorsEquiv, Equiv.trans, Equiv.sigmaCongrRight,
    Equiv.sigmaFiberEquiv] ; rfl

/-- The generator projection remains the original source simplex. -/
theorem nativeCoverPullbackSimplexPathGeneratorsEquiv_projection
    {X Y : SSet.{u}} (f : X ⟶ Y) (y : Y _⦋0⦌) (n : ℕ)
    (g : nativeCoverPullbackSimplexPathGenerators f y n) :
    (pullback.fst f (nativeCoverProjection Y y)).app (Opposite.op ⦋n⦌)
        (nativeCoverPullbackSimplexPathGeneratorsEquiv f y n g) =
      (SSet.yonedaEquiv (X := X) (n := ⦋n⦌)) g.1 := by
  let L := (nativeCoverPullbackSimplexPathEquiv f y g.1).symm g.2
  have hL : L.val ≫ pullback.fst f (nativeCoverProjection Y y) = g.1 := L.property
  exact (congrArg (fun s : (pullback f (nativeCoverProjection Y y)) _⦋n⦌ =>
      (pullback.fst f (nativeCoverProjection Y y)).app (Opposite.op ⦋n⦌) s)
    (nativeCoverPullbackSimplexPathGeneratorsEquiv_apply f y n g)).trans
      ((SSet.yonedaEquiv_comp L.val (pullback.fst f (nativeCoverProjection Y y))).symm.trans
        (congrArg (SSet.yonedaEquiv (X := X) (n := ⦋n⦌)) hL))

/-- The inverse recovers every source-simplex and original target-path pair. -/
theorem nativeCoverPullbackSimplexPathGeneratorsEquiv_left_inv
    {X Y : SSet.{u}} (f : X ⟶ Y) (y : Y _⦋0⦌) (n : ℕ)
    (g : nativeCoverPullbackSimplexPathGenerators f y n) :
    (nativeCoverPullbackSimplexPathGeneratorsEquiv f y n).symm
      (nativeCoverPullbackSimplexPathGeneratorsEquiv f y n g) = g :=
  (nativeCoverPullbackSimplexPathGeneratorsEquiv f y n).symm_apply_apply g

/-- The forward map recovers every simplex in the literal pulled-back cover. -/
theorem nativeCoverPullbackSimplexPathGeneratorsEquiv_right_inv
    {X Y : SSet.{u}} (f : X ⟶ Y) (y : Y _⦋0⦌) (n : ℕ)
    (s : (pullback f (nativeCoverProjection Y y)) _⦋n⦌) :
    nativeCoverPullbackSimplexPathGeneratorsEquiv f y n
      ((nativeCoverPullbackSimplexPathGeneratorsEquiv f y n).symm s) = s :=
  (nativeCoverPullbackSimplexPathGeneratorsEquiv f y n).apply_symm_apply s

end SSet.KanComplex

namespace SSet.KanComplex

/-- The target transport retains the association cast to the restricted source simplex. -/
def nativeCoverPullbackSimplexPathTransport
    {X Y : SSet.{u}} (f : X ⟶ Y) {m n : ℕ}
    (σ : (Δ[n] : SSet.{u}) ⟶ X) (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    let αn : (Δ[0] : SSet.{u}) ⟶ Δ[n] := SSet.yonedaEquiv.symm
      (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1)))
    let αm : (Δ[0] : SSet.{u}) ⟶ Δ[m] := SSet.yonedaEquiv.symm
      (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin (m + 1)))
    SSet.FundamentalGroupoid.mk ((SSet.yonedaEquiv (n := ⦋0⦌)) (αn ≫ (σ ≫ f))) ⟶
      SSet.FundamentalGroupoid.mk ((SSet.yonedaEquiv (n := ⦋0⦌))
        (αm ≫ ((SSet.stdSimplex.map θ ≫ σ) ≫ f))) :=
  let αm : (Δ[0] : SSet.{u}) ⟶ Δ[m] := SSet.yonedaEquiv.symm
    (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin (m + 1)))
  nativeCoverSimplexPathTransport (σ ≫ f) θ ≫ eqToHom
    (congrArg (fun τ : (Δ[m] : SSet.{u}) ⟶ Y => SSet.FundamentalGroupoid.mk
      ((SSet.yonedaEquiv (n := ⦋0⦌)) (αm ≫ τ)))
      (Category.assoc (SSet.stdSimplex.map θ) σ f).symm)

private theorem nativePathCoordinate_baseCast
    {Y : SSet.{u}} {y : Y _⦋0⦌} {n : ℕ}
    {τ τ' : (Δ[n] : SSet.{u}) ⟶ Y} (h : τ = τ')
    (T : {T : (Δ[n] : SSet.{u}) ⟶ nativeCover Y y // T ≫ nativeCoverProjection Y y = τ}) :
    let α : (Δ[0] : SSet.{u}) ⟶ Δ[n] := SSet.yonedaEquiv.symm
      (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1)))
    nativeCoverSimplexFiberPathEquiv τ' ⟨T.val, T.property.trans h⟩ =
      nativeCoverSimplexFiberPathEquiv τ T ≫ eqToHom
        (congrArg (fun ζ : (Δ[n] : SSet.{u}) ⟶ Y => SSet.FundamentalGroupoid.mk
          ((SSet.yonedaEquiv (n := ⦋0⦌)) (α ≫ ζ))) h) := by
  subst τ'
  change nativeCoverSimplexFiberPathEquiv τ T = nativeCoverSimplexFiberPathEquiv τ T ≫ 𝟙 _
  exact (Category.comp_id (nativeCoverSimplexFiberPathEquiv τ T)).symm

/-- Actual pullback restriction follows snd, native target restriction, and its derived endpoint
cast. -/
theorem nativeCoverPullbackSimplexPathEquiv_restrict
    {X Y : SSet.{u}} (f : X ⟶ Y) (y : Y _⦋0⦌) {m n : ℕ}
    (σ : (Δ[n] : SSet.{u}) ⟶ X) (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (L : {L : (Δ[n] : SSet.{u}) ⟶ pullback f (nativeCoverProjection Y y) //
      L ≫ pullback.fst f (nativeCoverProjection Y y) = σ}) :
    nativeCoverPullbackSimplexPathEquiv f y (SSet.stdSimplex.map θ ≫ σ)
        ⟨SSet.stdSimplex.map θ ≫ L.val, (Category.assoc _ _ _).trans
          (congrArg (fun g : (Δ[n] : SSet.{u}) ⟶ X => SSet.stdSimplex.map θ ≫ g)
            L.property)⟩ =
      nativeCoverPullbackSimplexPathEquiv f y σ L ≫
        nativeCoverPullbackSimplexPathTransport f σ θ := by
  let P : SSet.{u} := nativeCover Y y
  let p : P ⟶ Y := nativeCoverProjection Y y
  let W : SSet.{u} := pullback f p
  let q : W ⟶ X := pullback.fst f p
  let r : W ⟶ P := pullback.snd f p
  let a : (Δ[m] : SSet.{u}) ⟶ Δ[n] := SSet.stdSimplex.map θ
  let σ' : (Δ[m] : SSet.{u}) ⟶ X := a ≫ σ
  let L' : {K : (Δ[m] : SSet.{u}) ⟶ W // K ≫ q = σ'} :=
    ⟨a ≫ L.val, (Category.assoc _ _ _).trans (congrArg (fun g => a ≫ g) L.property)⟩
  let T : {K : (Δ[n] : SSet.{u}) ⟶ P // K ≫ p = σ ≫ f} :=
    nativeCoverPullbackSimplexFiberEquiv f y σ L
  let Tθ : {K : (Δ[m] : SSet.{u}) ⟶ P // K ≫ p = a ≫ (σ ≫ f)} :=
    ⟨a ≫ T.val, (Category.assoc _ _ _).trans (congrArg (fun g => a ≫ g) T.property)⟩
  let h : a ≫ (σ ≫ f) = σ' ≫ f := (Category.assoc a σ f).symm
  let U : {K : (Δ[m] : SSet.{u}) ⟶ P // K ≫ p = σ' ≫ f} :=
    nativeCoverPullbackSimplexFiberEquiv f y σ' L'
  let α : (Δ[0] : SSet.{u}) ⟶ Δ[m] := SSet.yonedaEquiv.symm
    (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin (m + 1)))
  let κ := congrArg (fun ζ : (Δ[m] : SSet.{u}) ⟶ Y => SSet.FundamentalGroupoid.mk
    ((SSet.yonedaEquiv (n := ⦋0⦌)) (α ≫ ζ))) h
  have hU : U = ⟨Tθ.val, Tθ.property.trans h⟩ := by
    apply Subtype.ext
    exact (nativeCoverPullbackSimplexFiberEquiv_apply f y σ' L').trans
      ((Category.assoc a L.val r).trans (congrArg (fun K : (Δ[n] : SSet.{u}) ⟶ P => a ≫ K)
        (nativeCoverPullbackSimplexFiberEquiv_apply f y σ L).symm))
  change nativeCoverSimplexFiberPathEquiv (σ' ≫ f) U =
    nativeCoverSimplexFiberPathEquiv (σ ≫ f) T ≫ nativeCoverPullbackSimplexPathTransport f σ θ
  exact (congrArg (nativeCoverSimplexFiberPathEquiv (σ' ≫ f)) hU).trans
    ((nativePathCoordinate_baseCast h Tθ).trans
      ((congrArg (fun γ => γ ≫ eqToHom κ)
        (nativeCoverSimplexFiberPathEquiv_restrict (σ ≫ f) θ T)).trans
        (Category.assoc (nativeCoverSimplexFiberPathEquiv (σ ≫ f) T)
          (nativeCoverSimplexPathTransport (σ ≫ f) θ) (eqToHom κ))))

/-- Direct restrictions use only the original source simplex and its original target path. -/
def nativeCoverPullbackSimplexPathGeneratorsRestriction
    {X Y : SSet.{u}} (f : X ⟶ Y) (y : Y _⦋0⦌) {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    nativeCoverPullbackSimplexPathGenerators f y n →
      nativeCoverPullbackSimplexPathGenerators f y m :=
  fun g => ⟨SSet.stdSimplex.map θ ≫ g.1, g.2 ≫ nativeCoverPullbackSimplexPathTransport f g.1 θ⟩

/-- Direct generator restriction agrees with restriction in the literal pullback cover. -/
theorem nativeCoverPullbackSimplexPathGeneratorsEquiv_restrict
    {X Y : SSet.{u}} (f : X ⟶ Y) (y : Y _⦋0⦌) {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (g : nativeCoverPullbackSimplexPathGenerators f y n) :
    nativeCoverPullbackSimplexPathGeneratorsEquiv f y m
        (nativeCoverPullbackSimplexPathGeneratorsRestriction f y θ g) =
      (pullback f (nativeCoverProjection Y y)).map θ.op
        (nativeCoverPullbackSimplexPathGeneratorsEquiv f y n g) := by
  rcases g with ⟨σ, γ⟩
  let W : SSet.{u} := pullback f (nativeCoverProjection Y y)
  let q : W ⟶ X := pullback.fst f (nativeCoverProjection Y y)
  let σ' : (Δ[m] : SSet.{u}) ⟶ X := SSet.stdSimplex.map θ ≫ σ
  let L : {K : (Δ[n] : SSet.{u}) ⟶ W // K ≫ q = σ} :=
    (nativeCoverPullbackSimplexPathEquiv f y σ).symm γ
  let L' : {K : (Δ[m] : SSet.{u}) ⟶ W // K ≫ q = σ'} :=
    ⟨SSet.stdSimplex.map θ ≫ L.val, (Category.assoc _ _ _).trans
      (congrArg (fun g : (Δ[n] : SSet.{u}) ⟶ X => SSet.stdSimplex.map θ ≫ g) L.property)⟩
  have hc : nativeCoverPullbackSimplexPathEquiv f y σ' L' =
      γ ≫ nativeCoverPullbackSimplexPathTransport f σ θ :=
    (nativeCoverPullbackSimplexPathEquiv_restrict f y σ θ L).trans
      (congrArg (fun δ => δ ≫ nativeCoverPullbackSimplexPathTransport f σ θ)
        ((nativeCoverPullbackSimplexPathEquiv f y σ).apply_symm_apply γ))
  have hL : (nativeCoverPullbackSimplexPathEquiv f y σ').symm
      (γ ≫ nativeCoverPullbackSimplexPathTransport f σ θ) = L' :=
    (nativeCoverPullbackSimplexPathEquiv f y σ').symm_apply_eq.mpr hc.symm
  exact (nativeCoverPullbackSimplexPathGeneratorsEquiv_apply f y m
      ⟨σ', γ ≫ nativeCoverPullbackSimplexPathTransport f σ θ⟩).trans
    ((congrArg (fun K : {K : (Δ[m] : SSet.{u}) ⟶ W // K ≫ q = σ'} =>
        (SSet.yonedaEquiv (X := W) (n := ⦋m⦌)) K.val) hL).trans
      ((SSet.yonedaEquiv_naturality θ L.val).symm.trans
        (congrArg (fun s : W _⦋n⦌ => W.map θ.op s)
          (nativeCoverPullbackSimplexPathGeneratorsEquiv_apply f y n ⟨σ, γ⟩).symm)))

/-- The independent literal-pullback generator restriction preserves identity. -/
theorem nativeCoverPullbackSimplexPathGeneratorsRestriction_id
    {X Y : SSet.{u}} (f : X ⟶ Y) (y : Y _⦋0⦌) (n : ℕ)
    (g : nativeCoverPullbackSimplexPathGenerators f y n) :
    nativeCoverPullbackSimplexPathGeneratorsRestriction f y (𝟙 ⦋n⦌) g = g := by
  apply (nativeCoverPullbackSimplexPathGeneratorsEquiv f y n).injective
  exact (nativeCoverPullbackSimplexPathGeneratorsEquiv_restrict f y (𝟙 ⦋n⦌) g).trans
    (congrArg (fun h : (pullback f (nativeCoverProjection Y y)) _⦋n⦌ ⟶
        (pullback f (nativeCoverProjection Y y)) _⦋n⦌ =>
        h (nativeCoverPullbackSimplexPathGeneratorsEquiv f y n g))
      ((pullback f (nativeCoverProjection Y y)).map_id (Opposite.op ⦋n⦌)))

/-- Direct literal-pullback restrictions compose in the original opposite-simplex order. -/
theorem nativeCoverPullbackSimplexPathGeneratorsRestriction_comp
    {X Y : SSet.{u}} (f : X ⟶ Y) (y : Y _⦋0⦌) {l m n : ℕ}
    (θ : ⦋m⦌ ⟶ ⦋n⦌) (ρ : ⦋l⦌ ⟶ ⦋m⦌)
    (g : nativeCoverPullbackSimplexPathGenerators f y n) :
    nativeCoverPullbackSimplexPathGeneratorsRestriction f y ρ
        (nativeCoverPullbackSimplexPathGeneratorsRestriction f y θ g) =
      nativeCoverPullbackSimplexPathGeneratorsRestriction f y (ρ ≫ θ) g := by
  apply (nativeCoverPullbackSimplexPathGeneratorsEquiv f y l).injective
  have hP : (pullback f (nativeCoverProjection Y y)).map (ρ ≫ θ).op
        (nativeCoverPullbackSimplexPathGeneratorsEquiv f y n g) =
      (pullback f (nativeCoverProjection Y y)).map ρ.op
        ((pullback f (nativeCoverProjection Y y)).map θ.op
          (nativeCoverPullbackSimplexPathGeneratorsEquiv f y n g)) :=
    congrArg (fun h : (pullback f (nativeCoverProjection Y y)) _⦋n⦌ ⟶
      (pullback f (nativeCoverProjection Y y)) _⦋l⦌ =>
      h (nativeCoverPullbackSimplexPathGeneratorsEquiv f y n g))
      ((pullback f (nativeCoverProjection Y y)).map_comp θ.op ρ.op)
  exact (nativeCoverPullbackSimplexPathGeneratorsEquiv_restrict f y ρ
      (nativeCoverPullbackSimplexPathGeneratorsRestriction f y θ g)).trans
    ((congrArg (fun s : (pullback f (nativeCoverProjection Y y)) _⦋m⦌ =>
      (pullback f (nativeCoverProjection Y y)).map ρ.op s)
      (nativeCoverPullbackSimplexPathGeneratorsEquiv_restrict f y θ g)).trans
      (hP.symm.trans (nativeCoverPullbackSimplexPathGeneratorsEquiv_restrict f y (ρ ≫ θ) g).symm))

/-- Arbitrary-target-point generators with their directly specified restrictions. -/
def nativeCoverPullbackSimplexPathGeneratorSSet
    {X Y : SSet.{u}} (f : X ⟶ Y) (y : Y _⦋0⦌) : SSet.{u} where
  obj d := nativeCoverPullbackSimplexPathGenerators f y d.unop.len
  map α := TypeCat.ofHom (nativeCoverPullbackSimplexPathGeneratorsRestriction f y α.unop)
  map_id d := by
    apply ConcreteCategory.ext_apply
    intro g
    change nativeCoverPullbackSimplexPathGeneratorsRestriction f y (𝟙 ⦋d.unop.len⦌) g = g
    exact nativeCoverPullbackSimplexPathGeneratorsRestriction_id f y d.unop.len g
  map_comp α β := by
    apply ConcreteCategory.ext_apply
    intro g
    change nativeCoverPullbackSimplexPathGeneratorsRestriction f y (β.unop ≫ α.unop) g =
      nativeCoverPullbackSimplexPathGeneratorsRestriction f y β.unop
        (nativeCoverPullbackSimplexPathGeneratorsRestriction f y α.unop g)
    exact (nativeCoverPullbackSimplexPathGeneratorsRestriction_comp f y α.unop β.unop g).symm

/-- The actual pointwise pullback-lift equivalences give a genuine natural isomorphism. -/
noncomputable def nativeCoverPullbackSimplexPathGeneratorIso
    {X Y : SSet.{u}} (f : X ⟶ Y) (y : Y _⦋0⦌) :
    nativeCoverPullbackSimplexPathGeneratorSSet f y ≅ pullback f (nativeCoverProjection Y y) :=
  NatIso.ofComponents
    (F := nativeCoverPullbackSimplexPathGeneratorSSet f y)
    (G := pullback f (nativeCoverProjection Y y))
    (fun d => (nativeCoverPullbackSimplexPathGeneratorsEquiv f y d.unop.len).toIso) (by
      intro a b α
      apply ConcreteCategory.ext_apply
      intro g
      change nativeCoverPullbackSimplexPathGeneratorsEquiv f y b.unop.len
          (nativeCoverPullbackSimplexPathGeneratorsRestriction f y α.unop g) =
        (pullback f (nativeCoverProjection Y y)).map α
          (nativeCoverPullbackSimplexPathGeneratorsEquiv f y a.unop.len g)
      exact nativeCoverPullbackSimplexPathGeneratorsEquiv_restrict f y α.unop g)

/-- The natural comparison keeps the actual literal-pullback inverse-lift forward map. -/
theorem nativeCoverPullbackSimplexPathGeneratorIso_hom_app
    {X Y : SSet.{u}} (f : X ⟶ Y) (y : Y _⦋0⦌) (n : ℕ)
    (g : nativeCoverPullbackSimplexPathGenerators f y n) :
    (nativeCoverPullbackSimplexPathGeneratorIso f y).hom.app (Opposite.op ⦋n⦌) g =
      nativeCoverPullbackSimplexPathGeneratorsEquiv f y n g := by
  dsimp only [nativeCoverPullbackSimplexPathGeneratorIso, NatIso.ofComponents, Equiv.toIso] ; rfl

end SSet.KanComplex

namespace SSet.KanComplex

/-- The actual map of fundamental groupoids sends the source first vertex to
the first vertex of the original image simplex. -/
theorem regularLocalCoefficientPullbackEndpoint_eq
    {X Y : SSet.{u}} (f : X ⟶ Y) {n : ℕ} (σ : (Δ[n] : SSet.{u}) ⟶ X) :
    let α : (Δ[0] : SSet.{u}) ⟶ Δ[n] := SSet.yonedaEquiv.symm
      (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1)))
    (SSet.mapFundamentalGroupoid f).obj
        (SSet.FundamentalGroupoid.mk ((SSet.yonedaEquiv (n := ⦋0⦌)) (α ≫ σ))) =
      SSet.FundamentalGroupoid.mk
        ((SSet.yonedaEquiv (n := ⦋0⦌)) (α ≫ (σ ≫ f))) := by
  let α : (Δ[0] : SSet.{u}) ⟶ Δ[n] := SSet.yonedaEquiv.symm
    (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1)))
  change SSet.FundamentalGroupoid.mk
      (f.app (Opposite.op ⦋0⦌) ((SSet.yonedaEquiv (n := ⦋0⦌)) (α ≫ σ))) = _
  exact (congrArg SSet.FundamentalGroupoid.mk
      (SSet.yonedaEquiv_comp (α ≫ σ) f).symm).trans
    (congrArg (fun τ : (Δ[0] : SSet.{u}) ⟶ Y => SSet.FundamentalGroupoid.mk
      ((SSet.yonedaEquiv (n := ⦋0⦌)) τ)) (Category.assoc α σ f))

/-- Original regular path indices for an arbitrary map identify with the
independently specified path generators of its literal pulled-back cover. -/
noncomputable def regularLocalCoefficientPullbackPathIndexEquiv
    {X Y : SSet.{u}} (f : X ⟶ Y) (y : Y _⦋0⦌) (n : ℕ) :
    regularLocalCoefficientPathGenerators
      (SSet.mapFundamentalGroupoid f) (SSet.FundamentalGroupoid.mk y) n ≃
      nativeCoverPullbackSimplexPathGenerators f y n :=
  Equiv.sigmaCongrRight (fun σ : (Δ[n] : SSet.{u}) ⟶ X =>
    Iso.homCongr (Iso.refl (SSet.FundamentalGroupoid.mk y))
      (eqToIso (regularLocalCoefficientPullbackEndpoint_eq f σ)))

/-- The index comparison leaves the original simplex and target path intact,
postcomposing only with the computed first-vertex cast. -/
theorem regularLocalCoefficientPullbackPathIndexEquiv_apply
    {X Y : SSet.{u}} (f : X ⟶ Y) (y : Y _⦋0⦌) (n : ℕ)
    (p : regularLocalCoefficientPathGenerators
      (SSet.mapFundamentalGroupoid f) (SSet.FundamentalGroupoid.mk y) n) :
    regularLocalCoefficientPullbackPathIndexEquiv f y n p =
      ⟨p.1, p.2 ≫ eqToHom (regularLocalCoefficientPullbackEndpoint_eq f p.1)⟩ := by
  rcases p with ⟨σ, γ⟩
  change (⟨σ, 𝟙 _ ≫ (γ ≫ eqToHom
    (regularLocalCoefficientPullbackEndpoint_eq f σ))⟩ :
      nativeCoverPullbackSimplexPathGenerators f y n) = _
  exact congrArg (fun δ => (⟨σ, δ⟩ : nativeCoverPullbackSimplexPathGenerators f y n))
    (Category.id_comp (γ ≫ eqToHom (regularLocalCoefficientPullbackEndpoint_eq f σ)))

/-- The existing original coefficient degree object has the actual integral
basis indexed by simplices of the original pulled-back covering model. -/
noncomputable def regularLocalCoefficientPullbackIntegralBasisIso
    {X Y : SSet.{u}} (f : X ⟶ Y) (y : Y _⦋0⦌) (n : ℕ) :
    SSet.localCoefficientObj ((SSet.mapFundamentalGroupoid f) ⋙
      CategoryTheory.regularPathModuleCoefficientFunctor (SSet.FundamentalGroupoid.mk y)) n ≅
      ∐ fun _ : nativeCoverPullbackSimplexPathGenerators f y n =>
        ModuleCat.of ℤ (ULift.{u} ℤ) :=
  (regularLocalCoefficientIntegralBasisIso
    (SSet.mapFundamentalGroupoid f) (SSet.FundamentalGroupoid.mk y) n) ≪≫
    (Limits.Sigma.whiskerEquiv (regularLocalCoefficientPullbackPathIndexEquiv f y n)
      (fun _ => Iso.refl (ModuleCat.of ℤ (ULift.{u} ℤ))))

/-- Every original path generator, with every integer coefficient, is sent to
the computed generator of the actual literal pullback. -/
theorem regularLocalCoefficientPullbackIntegralBasisIso_hom_ι_basis
    {X Y : SSet.{u}} (f : X ⟶ Y) (y : Y _⦋0⦌) (n : ℕ)
    (s : X _⦋n⦌)
    (γ : SSet.FundamentalGroupoid.mk y ⟶ (SSet.mapFundamentalGroupoid f).obj
      (ComposableArrows.left
        ((SSet.fundamentalGroupoidNerveUnit X).app (Opposite.op ⦋n⦌) s))) (z : ℤ) :
    (regularLocalCoefficientPullbackIntegralBasisIso f y n).hom
        (CategoryTheory.CategoryHomology.nervePullbackCoefficientι
          (SSet.fundamentalGroupoidNerveUnit X)
          ((SSet.mapFundamentalGroupoid f) ⋙ CategoryTheory.regularPathModuleCoefficientFunctor
            (SSet.FundamentalGroupoid.mk y)) s (z • FreeAbelianGroup.of γ)) =
      Limits.Sigma.ι (fun _ : nativeCoverPullbackSimplexPathGenerators f y n =>
        ModuleCat.of ℤ (ULift.{u} ℤ))
        ((regularLocalCoefficientPullbackPathIndexEquiv f y n)
          ((regularLocalCoefficientPathIndexEquiv (SSet.mapFundamentalGroupoid f)
            (SSet.FundamentalGroupoid.mk y) n) ⟨s, γ⟩)) (ULift.up z) := by
  let F := SSet.mapFundamentalGroupoid f
  let b := SSet.FundamentalGroupoid.mk y
  let P := regularLocalCoefficientPathGenerators F b n
  let E := regularLocalCoefficientPathIndexEquiv F b n
  let Q := regularLocalCoefficientPullbackPathIndexEquiv f y n
  let Z : ModuleCat.{u} ℤ := ModuleCat.of ℤ (ULift.{u} ℤ)
  let W := Limits.Sigma.whiskerEquiv
    (f := fun _ : P => Z)
    (g := fun _ : nativeCoverPullbackSimplexPathGenerators f y n => Z)
    Q (fun _ => Iso.refl Z)
  have hi : (regularLocalCoefficientIntegralBasisIso F b n).hom
        (CategoryTheory.CategoryHomology.nervePullbackCoefficientι
          (SSet.fundamentalGroupoidNerveUnit X)
          (F ⋙ CategoryTheory.regularPathModuleCoefficientFunctor b) s
          (z • FreeAbelianGroup.of γ)) =
      Limits.Sigma.ι (fun _ : P => Z) (E ⟨s, γ⟩) (ULift.up z) :=
    (regularLocalCoefficientIntegralBasisIso_hom_ι_basis F b n s γ z).trans
      (congrArg (fun p : P => Limits.Sigma.ι (fun _ : P => Z) p (ULift.up z))
        (regularLocalCoefficientPathIndexEquiv_apply F b n s γ).symm)
  have hWm : Limits.Sigma.ι (fun _ : P => Z) (E ⟨s, γ⟩) ≫ W.hom =
      Limits.Sigma.ι (fun _ : nativeCoverPullbackSimplexPathGenerators f y n => Z)
        (Q (E ⟨s, γ⟩)) := by
    dsimp only [W]
    rw [Limits.Sigma.whiskerEquiv_hom, Limits.Sigma.ι_comp_map']
    exact Category.id_comp _
  have hW := congrArg
    (fun h : Z ⟶ (∐ fun _ : nativeCoverPullbackSimplexPathGenerators f y n => Z) =>
      h (ULift.up z)) hWm
  change W.hom ((regularLocalCoefficientIntegralBasisIso F b n).hom
    (CategoryTheory.CategoryHomology.nervePullbackCoefficientι
      (SSet.fundamentalGroupoidNerveUnit X)
      (F ⋙ CategoryTheory.regularPathModuleCoefficientFunctor b) s
      (z • FreeAbelianGroup.of γ))) = _
  exact (congrArg
    (fun a : ((∐ fun _ : P => Z) : ModuleCat.{u} ℤ) => W.hom a) hi).trans hW

/-- The inverse computes the original simplex and path preimage and preserves
each integer weight, including empty path families. -/
theorem regularLocalCoefficientPullbackIntegralBasisIso_inv_ι_basis
    {X Y : SSet.{u}} (f : X ⟶ Y) (y : Y _⦋0⦌) (n : ℕ)
    (p : nativeCoverPullbackSimplexPathGenerators f y n) (z : ℤ) :
    let r := (regularLocalCoefficientPullbackPathIndexEquiv f y n).symm p
    let q := (regularLocalCoefficientPathIndexEquiv (SSet.mapFundamentalGroupoid f)
      (SSet.FundamentalGroupoid.mk y) n).symm r
    (regularLocalCoefficientPullbackIntegralBasisIso f y n).inv
        (Limits.Sigma.ι (fun _ : nativeCoverPullbackSimplexPathGenerators f y n =>
          ModuleCat.of ℤ (ULift.{u} ℤ)) p (ULift.up z)) =
      CategoryTheory.CategoryHomology.nervePullbackCoefficientι
        (SSet.fundamentalGroupoidNerveUnit X)
        ((SSet.mapFundamentalGroupoid f) ⋙ CategoryTheory.regularPathModuleCoefficientFunctor
          (SSet.FundamentalGroupoid.mk y)) q.1 (z • FreeAbelianGroup.of q.2) := by
  let F := SSet.mapFundamentalGroupoid f
  let b := SSet.FundamentalGroupoid.mk y
  let E := regularLocalCoefficientPathIndexEquiv F b n
  let Q := regularLocalCoefficientPullbackPathIndexEquiv f y n
  let r := Q.symm p
  let q := E.symm r
  let A := regularLocalCoefficientPullbackIntegralBasisIso f y n
  let Z : ModuleCat.{u} ℤ := ModuleCat.of ℤ (ULift.{u} ℤ)
  have hq : Q (E q) = p :=
    (congrArg Q (E.apply_symm_apply r)).trans (Q.apply_symm_apply p)
  have hf := (regularLocalCoefficientPullbackIntegralBasisIso_hom_ι_basis
      f y n q.1 q.2 z).trans
    (congrArg (fun t : nativeCoverPullbackSimplexPathGenerators f y n =>
      Limits.Sigma.ι (fun _ : nativeCoverPullbackSimplexPathGenerators f y n => Z)
        t (ULift.up z)) hq)
  have hi : A.inv
        (A.hom (CategoryTheory.CategoryHomology.nervePullbackCoefficientι
          (SSet.fundamentalGroupoidNerveUnit X)
          (F ⋙ CategoryTheory.regularPathModuleCoefficientFunctor b) q.1
          (z • FreeAbelianGroup.of q.2))) =
      CategoryTheory.CategoryHomology.nervePullbackCoefficientι
        (SSet.fundamentalGroupoidNerveUnit X)
        (F ⋙ CategoryTheory.regularPathModuleCoefficientFunctor b) q.1
        (z • FreeAbelianGroup.of q.2) :=
    congrArg (fun h : SSet.localCoefficientObj
      (F ⋙ CategoryTheory.regularPathModuleCoefficientFunctor b) n ⟶
      SSet.localCoefficientObj (F ⋙ CategoryTheory.regularPathModuleCoefficientFunctor b) n =>
      h (CategoryTheory.CategoryHomology.nervePullbackCoefficientι
        (SSet.fundamentalGroupoidNerveUnit X)
        (F ⋙ CategoryTheory.regularPathModuleCoefficientFunctor b) q.1
        (z • FreeAbelianGroup.of q.2))) A.hom_inv_id
  exact (congrArg
    (fun a : ((∐ fun _ : nativeCoverPullbackSimplexPathGenerators f y n => Z) :
      ModuleCat.{u} ℤ) => A.inv a) hf.symm).trans hi

end SSet.KanComplex

namespace SSet.KanComplex

/-- The actual unit chain of an image simplex is the original unit chain mapped through f. -/
theorem nativeCoverUnitChain_mapFundamentalGroupoid
    {X Y : SSet.{u}} (f : X ⟶ Y) {n : ℕ} (σ : (Δ[n] : SSet.{u}) ⟶ X) :
    (SSet.yonedaEquiv (σ ≫ nativeCoverUnit X)) ⋙ SSet.mapFundamentalGroupoid f =
      SSet.yonedaEquiv ((σ ≫ f) ≫ nativeCoverUnit Y) := by
  let F : SSet.FundamentalGroupoid X ⥤ SSet.FundamentalGroupoid Y :=
    SSet.mapFundamentalGroupoid f
  have h0 : σ ≫ (nativeCoverUnit X ≫ CategoryTheory.nerveMap F) =
      (σ ≫ f) ≫ nativeCoverUnit Y :=
    (congrArg (fun η : X ⟶ CategoryTheory.nerve (SSet.FundamentalGroupoid Y) => σ ≫ η)
      (nativeCoverUnit_naturality f).symm).trans
      (Category.assoc σ f (nativeCoverUnit Y)).symm
  have h1 : (σ ≫ nativeCoverUnit X) ≫ CategoryTheory.nerveMap F =
      (σ ≫ f) ≫ nativeCoverUnit Y :=
    (Category.assoc σ (nativeCoverUnit X) (CategoryTheory.nerveMap F)).trans h0
  have hy := SSet.yonedaEquiv_comp (σ ≫ nativeCoverUnit X) (CategoryTheory.nerveMap F)
  change SSet.yonedaEquiv ((σ ≫ nativeCoverUnit X) ≫ CategoryTheory.nerveMap F) =
    (SSet.yonedaEquiv (σ ≫ nativeCoverUnit X)) ⋙ F at hy
  exact hy.symm.trans
    (congrArg (SSet.yonedaEquiv (X := CategoryTheory.nerve (SSet.FundamentalGroupoid Y))
      (n := ⦋n⦌)) h1)

/-- The actual native restriction path maps through f with the computed endpoint casts. -/
theorem nativeCoverSimplexPathTransport_mapFundamentalGroupoid
    {X Y : SSet.{u}} (f : X ⟶ Y) {m n : ℕ}
    (σ : (Δ[n] : SSet.{u}) ⟶ X) (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    (SSet.mapFundamentalGroupoid f).map (nativeCoverSimplexPathTransport σ θ) ≫
        eqToHom (regularLocalCoefficientPullbackEndpoint_eq f (SSet.stdSimplex.map θ ≫ σ)) =
      eqToHom (regularLocalCoefficientPullbackEndpoint_eq f σ) ≫
        nativeCoverPullbackSimplexPathTransport f σ θ := by
  let ΓX : Type u := SSet.FundamentalGroupoid X
  let ΓY : Type u := SSet.FundamentalGroupoid Y
  let F : ΓX ⥤ ΓY := SSet.mapFundamentalGroupoid f
  let T : ComposableArrows ΓX n := SSet.yonedaEquiv (σ ≫ nativeCoverUnit X)
  let S : ComposableArrows ΓY n := SSet.yonedaEquiv ((σ ≫ f) ≫ nativeCoverUnit Y)
  let j : Fin (n + 1) := θ.toOrderHom (0 : Fin (m + 1))
  let q : (0 : Fin (n + 1)) ⟶ j := homOfLE (Fin.zero_le j)
  let a : (Δ[m] : SSet.{u}) ⟶ Δ[n] := SSet.stdSimplex.map θ
  let αn : (Δ[0] : SSet.{u}) ⟶ Δ[n] := SSet.yonedaEquiv.symm
    (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1)))
  let αm : (Δ[0] : SSet.{u}) ⟶ Δ[m] := SSet.yonedaEquiv.symm
    (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin (m + 1)))
  let N : ΓX := SSet.FundamentalGroupoid.mk ((SSet.yonedaEquiv (n := ⦋0⦌)) (αn ≫ σ))
  let M : ΓX := SSet.FundamentalGroupoid.mk
    ((SSet.yonedaEquiv (n := ⦋0⦌)) (αm ≫ (a ≫ σ)))
  let U : ΓY := SSet.FundamentalGroupoid.mk
    ((SSet.yonedaEquiv (n := ⦋0⦌)) (αn ≫ (σ ≫ f)))
  let V : ΓY := SSet.FundamentalGroupoid.mk
    ((SSet.yonedaEquiv (n := ⦋0⦌)) (αm ≫ (a ≫ (σ ≫ f))))
  let W : ΓY := SSet.FundamentalGroupoid.mk
    ((SSet.yonedaEquiv (n := ⦋0⦌)) (αm ≫ ((a ≫ σ) ≫ f)))
  let κX0 : T.obj (0 : Fin (n + 1)) = N := nativeCoverUnitChain_firstVertex_eq σ
  let κXj : T.obj j = M := nativeCoverUnitChain_restrictedFirst_eq σ θ
  let κY0 : S.obj (0 : Fin (n + 1)) = U := nativeCoverUnitChain_firstVertex_eq (σ ≫ f)
  let κYj : S.obj j = V := nativeCoverUnitChain_restrictedFirst_eq (σ ≫ f) θ
  let χ0 : F.obj N = U := regularLocalCoefficientPullbackEndpoint_eq f σ
  let χj : F.obj M = W := regularLocalCoefficientPullbackEndpoint_eq f (a ≫ σ)
  let ν : V = W := congrArg (fun ζ : (Δ[m] : SSet.{u}) ⟶ Y =>
    SSet.FundamentalGroupoid.mk ((SSet.yonedaEquiv (n := ⦋0⦌)) (αm ≫ ζ)))
      (Category.assoc a σ f).symm
  have hU : T ⋙ F = S := nativeCoverUnitChain_mapFundamentalGroupoid f σ
  let e0 : F.obj (T.obj (0 : Fin (n + 1))) = S.obj (0 : Fin (n + 1)) :=
    Functor.congr_obj hU (0 : Fin (n + 1))
  let ej : F.obj (T.obj j) = S.obj j := Functor.congr_obj hU j
  have hq := Functor.congr_hom hU q
  change F.map (T.map q) = eqToHom e0 ≫ S.map q ≫ eqToHom ej.symm at hq
  let c0 : F.obj N = S.obj (0 : Fin (n + 1)) :=
    (congrArg F.obj κX0.symm).trans e0
  let cj : S.obj j = W := ej.symm.trans ((congrArg F.obj κXj).trans χj)
  have hc0 : eqToHom c0 = eqToHom (χ0.trans κY0.symm) :=
    congrArg (fun e : F.obj N = S.obj (0 : Fin (n + 1)) => eqToHom e)
      (Subsingleton.elim c0 (χ0.trans κY0.symm))
  have hcj : eqToHom cj = eqToHom (κYj.trans ν) :=
    congrArg (fun e : S.obj j = W => eqToHom e)
      (Subsingleton.elim cj (κYj.trans ν))
  have hmap : F.map (nativeCoverSimplexPathTransport σ θ) =
      F.map (eqToHom κX0.symm) ≫ F.map (T.map q) ≫ F.map (eqToHom κXj) := by
    change F.map (eqToHom κX0.symm ≫ T.map q ≫ eqToHom κXj) = _
    exact (F.map_comp (eqToHom κX0.symm) (T.map q ≫ eqToHom κXj)).trans
      (congrArg (fun h : F.obj (T.obj (0 : Fin (n + 1))) ⟶ F.obj M =>
        F.map (eqToHom κX0.symm) ≫ h) (F.map_comp (T.map q) (eqToHom κXj)))
  have hl : F.map (nativeCoverSimplexPathTransport σ θ) ≫ eqToHom χj =
      eqToHom (congrArg F.obj κX0.symm) ≫ F.map (T.map q) ≫
        eqToHom ((congrArg F.obj κXj).trans χj) := by
    rw [hmap]
    simp only [eqToHom_map, Category.assoc, eqToHom_trans]
  have hm : eqToHom (congrArg F.obj κX0.symm) ≫ F.map (T.map q) ≫
        eqToHom ((congrArg F.obj κXj).trans χj) =
      eqToHom c0 ≫ S.map q ≫ eqToHom cj := by
    have h := congrArg (fun h : F.obj (T.obj (0 : Fin (n + 1))) ⟶ F.obj (T.obj j) =>
      eqToHom (congrArg F.obj κX0.symm) ≫ h ≫
        eqToHom ((congrArg F.obj κXj).trans χj)) hq
    simpa only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans] using h
  have hm0 : eqToHom c0 ≫ S.map q ≫ eqToHom cj =
      eqToHom (χ0.trans κY0.symm) ≫ S.map q ≫ eqToHom cj :=
    congrArg (fun h : F.obj N ⟶ S.obj (0 : Fin (n + 1)) =>
      h ≫ S.map q ≫ eqToHom cj) hc0
  have hmj : eqToHom (χ0.trans κY0.symm) ≫ S.map q ≫ eqToHom cj =
      eqToHom (χ0.trans κY0.symm) ≫ S.map q ≫ eqToHom (κYj.trans ν) :=
    congrArg (fun h : S.obj j ⟶ W => eqToHom (χ0.trans κY0.symm) ≫ S.map q ≫ h) hcj
  have hr : eqToHom χ0 ≫ nativeCoverPullbackSimplexPathTransport f σ θ =
      eqToHom (χ0.trans κY0.symm) ≫ S.map q ≫ eqToHom (κYj.trans ν) := by
    change eqToHom χ0 ≫ ((eqToHom κY0.symm ≫ S.map q ≫ eqToHom κYj) ≫ eqToHom ν) = _
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
  change F.map (nativeCoverSimplexPathTransport σ θ) ≫ eqToHom χj =
    eqToHom χ0 ≫ nativeCoverPullbackSimplexPathTransport f σ θ
  exact hl.trans (hm.trans (hm0.trans (hmj.trans hr.symm)))

/-- The computed pullback path index equivalence preserves every direct restriction. -/
theorem regularLocalCoefficientPullbackPathIndexEquiv_restrict
    {X Y : SSet.{u}} (f : X ⟶ Y) (y : Y _⦋0⦌) {m n : ℕ}
    (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (p : regularLocalCoefficientPathGenerators
      (SSet.mapFundamentalGroupoid f) (SSet.FundamentalGroupoid.mk y) n) :
    regularLocalCoefficientPullbackPathIndexEquiv f y m
        (regularLocalCoefficientPathRestriction
          (SSet.mapFundamentalGroupoid f) (SSet.FundamentalGroupoid.mk y) θ p) =
      nativeCoverPullbackSimplexPathGeneratorsRestriction f y θ
        (regularLocalCoefficientPullbackPathIndexEquiv f y n p) := by
  rcases p with ⟨σ, γ⟩
  let F : SSet.FundamentalGroupoid X ⥤ SSet.FundamentalGroupoid Y :=
    SSet.mapFundamentalGroupoid f
  let b : SSet.FundamentalGroupoid Y := SSet.FundamentalGroupoid.mk y
  let a : (Δ[m] : SSet.{u}) ⟶ Δ[n] := SSet.stdSimplex.map θ
  let σ' : (Δ[m] : SSet.{u}) ⟶ X := a ≫ σ
  let αn : (Δ[0] : SSet.{u}) ⟶ Δ[n] := SSet.yonedaEquiv.symm
    (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1)))
  let αm : (Δ[0] : SSet.{u}) ⟶ Δ[m] := SSet.yonedaEquiv.symm
    (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin (m + 1)))
  let N : SSet.FundamentalGroupoid X := SSet.FundamentalGroupoid.mk
    ((SSet.yonedaEquiv (n := ⦋0⦌)) (αn ≫ σ))
  let M : SSet.FundamentalGroupoid X := SSet.FundamentalGroupoid.mk
    ((SSet.yonedaEquiv (n := ⦋0⦌)) (αm ≫ σ'))
  let U : SSet.FundamentalGroupoid Y := SSet.FundamentalGroupoid.mk
    ((SSet.yonedaEquiv (n := ⦋0⦌)) (αn ≫ (σ ≫ f)))
  let Z : SSet.FundamentalGroupoid Y := SSet.FundamentalGroupoid.mk
    ((SSet.yonedaEquiv (n := ⦋0⦌)) (αm ≫ (σ' ≫ f)))
  let χ0 : F.obj N = U := regularLocalCoefficientPullbackEndpoint_eq f σ
  let χm : F.obj M = Z := regularLocalCoefficientPullbackEndpoint_eq f σ'
  let β : N ⟶ M := nativeCoverSimplexPathTransport σ θ
  let βf : U ⟶ Z := nativeCoverPullbackSimplexPathTransport f σ θ
  have hβ : F.map β ≫ eqToHom χm = eqToHom χ0 ≫ βf :=
    nativeCoverSimplexPathTransport_mapFundamentalGroupoid f σ θ
  have hγ : (γ ≫ F.map β) ≫ eqToHom χm = (γ ≫ eqToHom χ0) ≫ βf :=
    (Category.assoc γ (F.map β) (eqToHom χm)).trans
      ((congrArg (fun h : F.obj N ⟶ Z => γ ≫ h) hβ).trans
        (Category.assoc γ (eqToHom χ0) βf).symm)
  have hl : regularLocalCoefficientPullbackPathIndexEquiv f y m
        (regularLocalCoefficientPathRestriction F b θ ⟨σ, γ⟩) =
      (⟨σ', (γ ≫ F.map β) ≫ eqToHom χm⟩ :
        nativeCoverPullbackSimplexPathGenerators f y m) :=
    regularLocalCoefficientPullbackPathIndexEquiv_apply f y m
      (regularLocalCoefficientPathRestriction F b θ ⟨σ, γ⟩)
  have hr : nativeCoverPullbackSimplexPathGeneratorsRestriction f y θ
        (regularLocalCoefficientPullbackPathIndexEquiv f y n ⟨σ, γ⟩) =
      (⟨σ', (γ ≫ eqToHom χ0) ≫ βf⟩ :
        nativeCoverPullbackSimplexPathGenerators f y m) := by
    have hQ := regularLocalCoefficientPullbackPathIndexEquiv_apply f y n
      (show regularLocalCoefficientPathGenerators F b n from ⟨σ, γ⟩)
    have hR : nativeCoverPullbackSimplexPathGeneratorsRestriction f y θ
          (regularLocalCoefficientPullbackPathIndexEquiv f y n
            (show regularLocalCoefficientPathGenerators F b n from ⟨σ, γ⟩)) =
        nativeCoverPullbackSimplexPathGeneratorsRestriction f y θ
          (⟨σ, γ ≫ eqToHom χ0⟩ : nativeCoverPullbackSimplexPathGenerators f y n) :=
      congrArg (fun p : nativeCoverPullbackSimplexPathGenerators f y n =>
        nativeCoverPullbackSimplexPathGeneratorsRestriction f y θ p) hQ
    have hpair : nativeCoverPullbackSimplexPathGeneratorsRestriction f y θ
          (⟨σ, γ ≫ eqToHom χ0⟩ : nativeCoverPullbackSimplexPathGenerators f y n) =
        (⟨σ', (γ ≫ eqToHom χ0) ≫ βf⟩ :
          nativeCoverPullbackSimplexPathGenerators f y m) := rfl
    exact hR.trans hpair
  have hp : (⟨σ', (γ ≫ F.map β) ≫ eqToHom χm⟩ :
        nativeCoverPullbackSimplexPathGenerators f y m) =
      ⟨σ', (γ ≫ eqToHom χ0) ≫ βf⟩ :=
    congrArg (fun δ : b ⟶ Z => (⟨σ', δ⟩ : nativeCoverPullbackSimplexPathGenerators f y m)) hγ
  exact hl.trans (hp.trans hr.symm)

end SSet.KanComplex


namespace SSet.KanComplex

/-- The actual original face component preserves every integer on each path generator. -/
theorem regularLocalCoefficientFaceHom_basis
    {X : SSet.{u}} {C : Type v} [Category.{u} C]
    (F : SSet.FundamentalGroupoid X ⥤ C) (y : C)
    {n : ℕ} (i : Fin (n + 2)) (s : X _⦋n + 1⦌)
    (γ : y ⟶ F.obj (ComposableArrows.left
      ((SSet.fundamentalGroupoidNerveUnit X).app (Opposite.op ⦋n + 1⦌) s))) (z : ℤ) :
    CategoryTheory.CategoryHomology.nervePullbackCoefficientFaceHom
        (SSet.fundamentalGroupoidNerveUnit X)
        (F ⋙ CategoryTheory.regularPathModuleCoefficientFunctor y) i s
        (z • FreeAbelianGroup.of γ) =
      z • FreeAbelianGroup.of
        ((regularLocalCoefficientOriginalPathRestriction F y (SimplexCategory.δ i)
          ⟨s, γ⟩).2) := by
  let Γ : Type u := SSet.FundamentalGroupoid X
  let η : X ⟶ CategoryTheory.nerve Γ := SSet.fundamentalGroupoidNerveUnit X
  let L := F ⋙ CategoryTheory.regularPathModuleCoefficientFunctor y
  let T : ComposableArrows Γ (n + 1) := η.app (Opposite.op ⦋n + 1⦌) s
  let t : X _⦋n⦌ := X.δ i s
  let S : ComposableArrows Γ (n) := η.app (Opposite.op ⦋n⦌) t
  let ε : (CategoryTheory.nerve Γ).δ i T = S :=
    CategoryTheory.CategoryHomology.nervePullback_face_index η i s
  let μ : ((CategoryTheory.nerve Γ).δ i T).left = S.left :=
    congrArg ComposableArrows.left ε
  let a : T.left ⟶ ((CategoryTheory.nerve Γ).δ i T).left :=
    CategoryTheory.CategoryHomology.faceLeftHom i T
  let q : T.left ⟶ S.left := a ≫ eqToHom μ
  have hc : eqToHom (congrArg L.obj μ) = L.map (eqToHom μ) := (eqToHom_map L μ).symm
  have hm : CategoryTheory.CategoryHomology.nervePullbackCoefficientFaceHom η L i s =
      L.map q := by
    change L.map a ≫ eqToHom (congrArg L.obj μ) = L.map q
    exact (congrArg (fun f : L.obj (((CategoryTheory.nerve Γ).δ i T).left) ⟶
      L.obj S.left => L.map a ≫ f) hc).trans (L.map_comp a (eqToHom μ)).symm
  have hγ : L.map q (FreeAbelianGroup.of γ) =
      FreeAbelianGroup.of (γ ≫ F.map q) :=
    CategoryTheory.regularPathModuleCoefficientFunctor_map_of y (F.map q) γ
  have hz : L.map q (z • FreeAbelianGroup.of γ) =
      z • FreeAbelianGroup.of (γ ≫ F.map q) :=
    ((L.map q).hom.map_smul z (FreeAbelianGroup.of γ)).trans
      (congrArg (fun b : FreeAbelianGroup (y ⟶ F.obj S.left) => z • b) hγ)
  change CategoryTheory.CategoryHomology.nervePullbackCoefficientFaceHom η L i s
      (z • FreeAbelianGroup.of γ) = z • FreeAbelianGroup.of (γ ≫ F.map q)
  exact (congrArg (fun f : L.obj T.left ⟶ L.obj S.left => f (z • FreeAbelianGroup.of γ))
    hm).trans hz

/-- The actual original degeneracy component preserves every integer on each path generator. -/
theorem regularLocalCoefficientDegeneracyHom_basis
    {X : SSet.{u}} {C : Type v} [Category.{u} C]
    (F : SSet.FundamentalGroupoid X ⥤ C) (y : C)
    {n : ℕ} (i : Fin (n + 1)) (s : X _⦋n⦌)
    (γ : y ⟶ F.obj (ComposableArrows.left
      ((SSet.fundamentalGroupoidNerveUnit X).app (Opposite.op ⦋n⦌) s))) (z : ℤ) :
    CategoryTheory.CategoryHomology.nervePullbackCoefficientDegeneracyHom
        (SSet.fundamentalGroupoidNerveUnit X)
        (F ⋙ CategoryTheory.regularPathModuleCoefficientFunctor y) i s
        (z • FreeAbelianGroup.of γ) =
      z • FreeAbelianGroup.of
        ((regularLocalCoefficientOriginalPathRestriction F y (SimplexCategory.σ i)
          ⟨s, γ⟩).2) := by
  let Γ : Type u := SSet.FundamentalGroupoid X
  let η : X ⟶ CategoryTheory.nerve Γ := SSet.fundamentalGroupoidNerveUnit X
  let L := F ⋙ CategoryTheory.regularPathModuleCoefficientFunctor y
  let T : ComposableArrows Γ (n) := η.app (Opposite.op ⦋n⦌) s
  let t : X _⦋n + 1⦌ := X.σ i s
  let S : ComposableArrows Γ (n + 1) := η.app (Opposite.op ⦋n + 1⦌) t
  let ε : (CategoryTheory.nerve Γ).σ i T = S :=
    CategoryTheory.CategoryHomology.nervePullback_degeneracy_index η i s
  let μ : ((CategoryTheory.nerve Γ).σ i T).left = S.left :=
    congrArg ComposableArrows.left ε
  let a : T.left ⟶ ((CategoryTheory.nerve Γ).σ i T).left :=
    CategoryTheory.CategoryHomology.degeneracyLeftHom i T
  let q : T.left ⟶ S.left := a ≫ eqToHom μ
  have hc : eqToHom (congrArg L.obj μ) = L.map (eqToHom μ) := (eqToHom_map L μ).symm
  have hm : CategoryTheory.CategoryHomology.nervePullbackCoefficientDegeneracyHom η L i s =
      L.map q := by
    change L.map a ≫ eqToHom (congrArg L.obj μ) = L.map q
    exact (congrArg (fun f : L.obj (((CategoryTheory.nerve Γ).σ i T).left) ⟶
      L.obj S.left => L.map a ≫ f) hc).trans (L.map_comp a (eqToHom μ)).symm
  have hγ : L.map q (FreeAbelianGroup.of γ) =
      FreeAbelianGroup.of (γ ≫ F.map q) :=
    CategoryTheory.regularPathModuleCoefficientFunctor_map_of y (F.map q) γ
  have hz : L.map q (z • FreeAbelianGroup.of γ) =
      z • FreeAbelianGroup.of (γ ≫ F.map q) :=
    ((L.map q).hom.map_smul z (FreeAbelianGroup.of γ)).trans
      (congrArg (fun b : FreeAbelianGroup (y ⟶ F.obj S.left) => z • b) hγ)
  change CategoryTheory.CategoryHomology.nervePullbackCoefficientDegeneracyHom η L i s
      (z • FreeAbelianGroup.of γ) = z • FreeAbelianGroup.of (γ ≫ F.map q)
  exact (congrArg (fun f : L.obj T.left ⟶ L.obj S.left => f (z • FreeAbelianGroup.of γ))
    hm).trans hz

/-- Direct module restrictions move independent path-pair indices and keep the integer unit. -/
noncomputable def regularLocalCoefficientPathModuleRestriction
    {X : SSet.{u}} {C : Type v} [Category.{u} C]
    (F : SSet.FundamentalGroupoid X ⥤ C) (y : C)
    {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    (∐ fun _ : regularLocalCoefficientPathGenerators F y n =>
      ModuleCat.of ℤ (ULift.{u} ℤ)) ⟶
    (∐ fun _ : regularLocalCoefficientPathGenerators F y m =>
      ModuleCat.of ℤ (ULift.{u} ℤ)) :=
  Limits.Sigma.map'
    (f := fun _ : regularLocalCoefficientPathGenerators F y m =>
      ModuleCat.of ℤ (ULift.{u} ℤ))
    (g := fun _ : regularLocalCoefficientPathGenerators F y n =>
      ModuleCat.of ℤ (ULift.{u} ℤ))
    (regularLocalCoefficientPathRestriction F y θ)
    (fun _ => 𝟙 (ModuleCat.of ℤ (ULift.{u} ℤ)))

/-- The independent module restriction has its literal original unit-summand formula. -/
theorem regularLocalCoefficientPathModuleRestriction_ι
    {X : SSet.{u}} {C : Type v} [Category.{u} C]
    (F : SSet.FundamentalGroupoid X ⥤ C) (y : C)
    {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) (a : regularLocalCoefficientPathGenerators F y n) :
    Limits.Sigma.ι (fun _ : regularLocalCoefficientPathGenerators F y n =>
        ModuleCat.of ℤ (ULift.{u} ℤ)) a ≫
      regularLocalCoefficientPathModuleRestriction F y θ =
    Limits.Sigma.ι (fun _ : regularLocalCoefficientPathGenerators F y m =>
      ModuleCat.of ℤ (ULift.{u} ℤ)) (regularLocalCoefficientPathRestriction F y θ a) := by
  change Limits.Sigma.ι (fun _ : regularLocalCoefficientPathGenerators F y n =>
      ModuleCat.of ℤ (ULift.{u} ℤ)) a ≫ Limits.Sigma.map'
    (f := fun _ : regularLocalCoefficientPathGenerators F y m =>
      ModuleCat.of ℤ (ULift.{u} ℤ))
    (g := fun _ : regularLocalCoefficientPathGenerators F y n =>
      ModuleCat.of ℤ (ULift.{u} ℤ))
    (regularLocalCoefficientPathRestriction F y θ)
    (fun _ => 𝟙 (ModuleCat.of ℤ (ULift.{u} ℤ))) = _
  exact (Limits.Sigma.ι_comp_map'
    (f := fun _ : regularLocalCoefficientPathGenerators F y m =>
      ModuleCat.of ℤ (ULift.{u} ℤ))
    (g := fun _ : regularLocalCoefficientPathGenerators F y n =>
      ModuleCat.of ℤ (ULift.{u} ℤ))
    (regularLocalCoefficientPathRestriction F y θ)
    (fun _ => 𝟙 (ModuleCat.of ℤ (ULift.{u} ℤ))) a).trans (Category.id_comp _)

/-- The entire original face map commutes with the independently defined degree comparison. -/
theorem regularLocalCoefficientIntegralBasisIso_face
    {X : SSet.{u}} {C : Type v} [Category.{u} C]
    (F : SSet.FundamentalGroupoid X ⥤ C) (y : C)
    {n : ℕ} (i : Fin (n + 2)) :
    SSet.localCoefficientFace (F ⋙ CategoryTheory.regularPathModuleCoefficientFunctor y) i ≫
        (regularLocalCoefficientIntegralBasisIso F y (n)).hom =
      (regularLocalCoefficientIntegralBasisIso F y (n + 1)).hom ≫
        regularLocalCoefficientPathModuleRestriction F y (SimplexCategory.δ i) := by
  let η := SSet.fundamentalGroupoidNerveUnit X
  let L := F ⋙ CategoryTheory.regularPathModuleCoefficientFunctor y
  let Z : ModuleCat.{u} ℤ := ModuleCat.of ℤ (ULift.{u} ℤ)
  let B : ModuleCat.{u} ℤ := ∐ fun _ : regularLocalCoefficientPathGenerators F y (n) => Z
  let A : ModuleCat.{u} ℤ := ∐ fun _ : regularLocalCoefficientPathGenerators F y (n + 1) => Z
  refine Limits.Sigma.hom_ext _ _ ?_
  intro s
  apply ModuleCat.hom_ext
  apply LinearMap.toAddMonoidHom_injective
  refine FreeAbelianGroup.lift_ext _ _ ?_
  intro γ
  let t : X _⦋n⦌ := X.δ i s
  let a := regularLocalCoefficientOriginalPathRestriction F y (SimplexCategory.δ i) ⟨s, γ⟩
  let δ : y ⟶ F.obj (ComposableArrows.left (η.app (Opposite.op ⦋n⦌) t)) := a.2
  let p : regularLocalCoefficientPathGenerators F y (n) :=
    regularLocalCoefficientPathIndexEquiv F y (n) a
  let q : regularLocalCoefficientPathGenerators F y (n + 1) :=
    regularLocalCoefficientPathIndexEquiv F y (n + 1) ⟨s, γ⟩
  let D := regularLocalCoefficientPathModuleRestriction F y (SimplexCategory.δ i)
  have hi : CategoryTheory.CategoryHomology.nervePullbackCoefficientι η L s ≫
        SSet.localCoefficientFace L i =
      CategoryTheory.CategoryHomology.nervePullbackCoefficientFaceHom η L i s ≫
        CategoryTheory.CategoryHomology.nervePullbackCoefficientι η L t :=
    CategoryTheory.CategoryHomology.nervePullbackCoefficientι_face η L i s
  have hb : CategoryTheory.CategoryHomology.nervePullbackCoefficientFaceHom η L i s
        (FreeAbelianGroup.of γ) = FreeAbelianGroup.of δ := by
    let A0 : ModuleCat.{u} ℤ := SSet.localCoefficientFamily L (n + 1) s
    let B0 : ModuleCat.{u} ℤ := SSet.localCoefficientFamily L n t
    let H : A0 ⟶ B0 :=
      CategoryTheory.CategoryHomology.nervePullbackCoefficientFaceHom η L i s
    have h1 : H ((1 : ℤ) • (FreeAbelianGroup.of γ : A0)) =
        (1 : ℤ) • (FreeAbelianGroup.of δ : B0) := by
      dsimp only [H, A0, B0, η, L, δ, a, t]
      exact regularLocalCoefficientFaceHom_basis F y i s γ (1 : ℤ)
    change H (FreeAbelianGroup.of γ : A0) = (FreeAbelianGroup.of δ : B0)
    exact (congrArg (fun b : A0 => H b)
      (one_smul ℤ (FreeAbelianGroup.of γ : A0)).symm).trans
        (h1.trans (one_smul ℤ (FreeAbelianGroup.of δ : B0)))
  have hv := congrArg (fun f : SSet.localCoefficientFamily L (n + 1) s ⟶
    SSet.localCoefficientObj L (n) => f (FreeAbelianGroup.of γ)) hi
  have hlocal : SSet.localCoefficientFace L i
        (CategoryTheory.CategoryHomology.nervePullbackCoefficientι η L s
          (FreeAbelianGroup.of γ)) =
      CategoryTheory.CategoryHomology.nervePullbackCoefficientι η L t
        (FreeAbelianGroup.of δ) :=
    hv.trans (congrArg (fun b : FreeAbelianGroup
      (y ⟶ F.obj (ComposableArrows.left (η.app (Opposite.op ⦋n⦌) t))) =>
      CategoryTheory.CategoryHomology.nervePullbackCoefficientι η L t b) hb)
  have hgl : (regularLocalCoefficientIntegralBasisIso F y (n)).hom
        (CategoryTheory.CategoryHomology.nervePullbackCoefficientι η L t
          (FreeAbelianGroup.of δ)) =
      Limits.Sigma.ι (fun _ : regularLocalCoefficientPathGenerators F y (n) => Z) p
        (ULift.up (1 : ℤ)) := by
    have h := regularLocalCoefficientIntegralBasisIso_hom_ι_basis F y (n) t δ (1 : ℤ)
    have h0 : (regularLocalCoefficientIntegralBasisIso F y (n)).hom
          (CategoryTheory.CategoryHomology.nervePullbackCoefficientι η L t
            (FreeAbelianGroup.of δ)) =
        Limits.Sigma.ι (fun _ : regularLocalCoefficientPathGenerators F y (n) => Z)
          ⟨SSet.yonedaEquiv.symm t,
            δ ≫ eqToHom (congrArg F.obj (regularLocalCoefficientFirstObject_eq t))⟩
          (ULift.up (1 : ℤ)) := by simpa only [one_zsmul] using h
    exact h0.trans (congrArg (fun b : regularLocalCoefficientPathGenerators F y (n) =>
      Limits.Sigma.ι (fun _ : regularLocalCoefficientPathGenerators F y (n) => Z) b
        (ULift.up (1 : ℤ)))
      (regularLocalCoefficientPathIndexEquiv_apply F y (n) t δ).symm)
  have hgr : (regularLocalCoefficientIntegralBasisIso F y (n + 1)).hom
        (CategoryTheory.CategoryHomology.nervePullbackCoefficientι η L s
          (FreeAbelianGroup.of γ)) =
      Limits.Sigma.ι (fun _ : regularLocalCoefficientPathGenerators F y (n + 1) => Z) q
        (ULift.up (1 : ℤ)) := by
    have h := regularLocalCoefficientIntegralBasisIso_hom_ι_basis F y (n + 1) s γ (1 : ℤ)
    have h0 : (regularLocalCoefficientIntegralBasisIso F y (n + 1)).hom
          (CategoryTheory.CategoryHomology.nervePullbackCoefficientι η L s
            (FreeAbelianGroup.of γ)) =
        Limits.Sigma.ι (fun _ : regularLocalCoefficientPathGenerators F y (n + 1) => Z)
          ⟨SSet.yonedaEquiv.symm s,
            γ ≫ eqToHom (congrArg F.obj (regularLocalCoefficientFirstObject_eq s))⟩
          (ULift.up (1 : ℤ)) := by simpa only [one_zsmul] using h
    exact h0.trans (congrArg (fun b : regularLocalCoefficientPathGenerators F y (n + 1) =>
      Limits.Sigma.ι (fun _ : regularLocalCoefficientPathGenerators F y (n + 1) => Z) b
        (ULift.up (1 : ℤ)))
      (regularLocalCoefficientPathIndexEquiv_apply F y (n + 1) s γ).symm)
  have hd : D
        (Limits.Sigma.ι (fun _ : regularLocalCoefficientPathGenerators F y (n + 1) => Z) q
          (ULift.up (1 : ℤ))) =
      Limits.Sigma.ι (fun _ : regularLocalCoefficientPathGenerators F y (n) => Z)
        (regularLocalCoefficientPathRestriction F y (SimplexCategory.δ i) q)
        (ULift.up (1 : ℤ)) :=
    congrArg (fun f : Z ⟶ B => f (ULift.up (1 : ℤ)))
      (regularLocalCoefficientPathModuleRestriction_ι F y (SimplexCategory.δ i) q)
  have hp : p = regularLocalCoefficientPathRestriction F y (SimplexCategory.δ i) q :=
    regularLocalCoefficientPathIndexEquiv_restrict F y (SimplexCategory.δ i) s γ
  have hunit := congrArg (fun b : regularLocalCoefficientPathGenerators F y (n) =>
    Limits.Sigma.ι (fun _ : regularLocalCoefficientPathGenerators F y (n) => Z) b
      (ULift.up (1 : ℤ))) hp
  have hleft := (congrArg (fun b : SSet.localCoefficientObj L (n) =>
    (regularLocalCoefficientIntegralBasisIso F y (n)).hom b) hlocal).trans hgl
  have hright := (congrArg (fun b : A => D b) hgr).trans hd
  change (regularLocalCoefficientIntegralBasisIso F y (n)).hom
      (SSet.localCoefficientFace L i
        (CategoryTheory.CategoryHomology.nervePullbackCoefficientι η L s
          (FreeAbelianGroup.of γ))) =
    D ((regularLocalCoefficientIntegralBasisIso F y (n + 1)).hom
      (CategoryTheory.CategoryHomology.nervePullbackCoefficientι η L s
        (FreeAbelianGroup.of γ)))
  exact hleft.trans (hunit.trans hright.symm)

/-- The entire original degeneracy map commutes with the independently defined degree comparison. -/
theorem regularLocalCoefficientIntegralBasisIso_degeneracy
    {X : SSet.{u}} {C : Type v} [Category.{u} C]
    (F : SSet.FundamentalGroupoid X ⥤ C) (y : C)
    {n : ℕ} (i : Fin (n + 1)) :
    SSet.localCoefficientDegeneracy (F ⋙ CategoryTheory.regularPathModuleCoefficientFunctor y) i ≫
        (regularLocalCoefficientIntegralBasisIso F y (n + 1)).hom =
      (regularLocalCoefficientIntegralBasisIso F y (n)).hom ≫
        regularLocalCoefficientPathModuleRestriction F y (SimplexCategory.σ i) := by
  let η := SSet.fundamentalGroupoidNerveUnit X
  let L := F ⋙ CategoryTheory.regularPathModuleCoefficientFunctor y
  let Z : ModuleCat.{u} ℤ := ModuleCat.of ℤ (ULift.{u} ℤ)
  let B : ModuleCat.{u} ℤ := ∐ fun _ : regularLocalCoefficientPathGenerators F y (n + 1) => Z
  let A : ModuleCat.{u} ℤ := ∐ fun _ : regularLocalCoefficientPathGenerators F y (n) => Z
  refine Limits.Sigma.hom_ext _ _ ?_
  intro s
  apply ModuleCat.hom_ext
  apply LinearMap.toAddMonoidHom_injective
  refine FreeAbelianGroup.lift_ext _ _ ?_
  intro γ
  let t : X _⦋n + 1⦌ := X.σ i s
  let a := regularLocalCoefficientOriginalPathRestriction F y (SimplexCategory.σ i) ⟨s, γ⟩
  let δ : y ⟶ F.obj (ComposableArrows.left (η.app (Opposite.op ⦋n + 1⦌) t)) := a.2
  let p : regularLocalCoefficientPathGenerators F y (n + 1) :=
    regularLocalCoefficientPathIndexEquiv F y (n + 1) a
  let q : regularLocalCoefficientPathGenerators F y (n) :=
    regularLocalCoefficientPathIndexEquiv F y (n) ⟨s, γ⟩
  let D := regularLocalCoefficientPathModuleRestriction F y (SimplexCategory.σ i)
  have hi : CategoryTheory.CategoryHomology.nervePullbackCoefficientι η L s ≫
        SSet.localCoefficientDegeneracy L i =
      CategoryTheory.CategoryHomology.nervePullbackCoefficientDegeneracyHom η L i s ≫
        CategoryTheory.CategoryHomology.nervePullbackCoefficientι η L t :=
    CategoryTheory.CategoryHomology.nervePullbackCoefficientι_degeneracy η L i s
  have hb : CategoryTheory.CategoryHomology.nervePullbackCoefficientDegeneracyHom η L i s
        (FreeAbelianGroup.of γ) = FreeAbelianGroup.of δ := by
    let A0 : ModuleCat.{u} ℤ := SSet.localCoefficientFamily L n s
    let B0 : ModuleCat.{u} ℤ := SSet.localCoefficientFamily L (n + 1) t
    let H : A0 ⟶ B0 :=
      CategoryTheory.CategoryHomology.nervePullbackCoefficientDegeneracyHom η L i s
    have h1 : H ((1 : ℤ) • (FreeAbelianGroup.of γ : A0)) =
        (1 : ℤ) • (FreeAbelianGroup.of δ : B0) := by
      dsimp only [H, A0, B0, η, L, δ, a, t]
      exact regularLocalCoefficientDegeneracyHom_basis F y i s γ (1 : ℤ)
    change H (FreeAbelianGroup.of γ : A0) = (FreeAbelianGroup.of δ : B0)
    exact (congrArg (fun b : A0 => H b)
      (one_smul ℤ (FreeAbelianGroup.of γ : A0)).symm).trans
        (h1.trans (one_smul ℤ (FreeAbelianGroup.of δ : B0)))
  have hv := congrArg (fun f : SSet.localCoefficientFamily L (n) s ⟶
    SSet.localCoefficientObj L (n + 1) => f (FreeAbelianGroup.of γ)) hi
  have hlocal : SSet.localCoefficientDegeneracy L i
        (CategoryTheory.CategoryHomology.nervePullbackCoefficientι η L s
          (FreeAbelianGroup.of γ)) =
      CategoryTheory.CategoryHomology.nervePullbackCoefficientι η L t
        (FreeAbelianGroup.of δ) :=
    hv.trans (congrArg (fun b : FreeAbelianGroup
      (y ⟶ F.obj (ComposableArrows.left (η.app (Opposite.op ⦋n + 1⦌) t))) =>
      CategoryTheory.CategoryHomology.nervePullbackCoefficientι η L t b) hb)
  have hgl : (regularLocalCoefficientIntegralBasisIso F y (n + 1)).hom
        (CategoryTheory.CategoryHomology.nervePullbackCoefficientι η L t
          (FreeAbelianGroup.of δ)) =
      Limits.Sigma.ι (fun _ : regularLocalCoefficientPathGenerators F y (n + 1) => Z) p
        (ULift.up (1 : ℤ)) := by
    have h := regularLocalCoefficientIntegralBasisIso_hom_ι_basis F y (n + 1) t δ (1 : ℤ)
    have h0 : (regularLocalCoefficientIntegralBasisIso F y (n + 1)).hom
          (CategoryTheory.CategoryHomology.nervePullbackCoefficientι η L t
            (FreeAbelianGroup.of δ)) =
        Limits.Sigma.ι (fun _ : regularLocalCoefficientPathGenerators F y (n + 1) => Z)
          ⟨SSet.yonedaEquiv.symm t,
            δ ≫ eqToHom (congrArg F.obj (regularLocalCoefficientFirstObject_eq t))⟩
          (ULift.up (1 : ℤ)) := by simpa only [one_zsmul] using h
    exact h0.trans (congrArg (fun b : regularLocalCoefficientPathGenerators F y (n + 1) =>
      Limits.Sigma.ι (fun _ : regularLocalCoefficientPathGenerators F y (n + 1) => Z) b
        (ULift.up (1 : ℤ)))
      (regularLocalCoefficientPathIndexEquiv_apply F y (n + 1) t δ).symm)
  have hgr : (regularLocalCoefficientIntegralBasisIso F y (n)).hom
        (CategoryTheory.CategoryHomology.nervePullbackCoefficientι η L s
          (FreeAbelianGroup.of γ)) =
      Limits.Sigma.ι (fun _ : regularLocalCoefficientPathGenerators F y (n) => Z) q
        (ULift.up (1 : ℤ)) := by
    have h := regularLocalCoefficientIntegralBasisIso_hom_ι_basis F y (n) s γ (1 : ℤ)
    have h0 : (regularLocalCoefficientIntegralBasisIso F y (n)).hom
          (CategoryTheory.CategoryHomology.nervePullbackCoefficientι η L s
            (FreeAbelianGroup.of γ)) =
        Limits.Sigma.ι (fun _ : regularLocalCoefficientPathGenerators F y (n) => Z)
          ⟨SSet.yonedaEquiv.symm s,
            γ ≫ eqToHom (congrArg F.obj (regularLocalCoefficientFirstObject_eq s))⟩
          (ULift.up (1 : ℤ)) := by simpa only [one_zsmul] using h
    exact h0.trans (congrArg (fun b : regularLocalCoefficientPathGenerators F y (n) =>
      Limits.Sigma.ι (fun _ : regularLocalCoefficientPathGenerators F y (n) => Z) b
        (ULift.up (1 : ℤ)))
      (regularLocalCoefficientPathIndexEquiv_apply F y (n) s γ).symm)
  have hd : D
        (Limits.Sigma.ι (fun _ : regularLocalCoefficientPathGenerators F y (n) => Z) q
          (ULift.up (1 : ℤ))) =
      Limits.Sigma.ι (fun _ : regularLocalCoefficientPathGenerators F y (n + 1) => Z)
        (regularLocalCoefficientPathRestriction F y (SimplexCategory.σ i) q)
        (ULift.up (1 : ℤ)) :=
    congrArg (fun f : Z ⟶ B => f (ULift.up (1 : ℤ)))
      (regularLocalCoefficientPathModuleRestriction_ι F y (SimplexCategory.σ i) q)
  have hp : p = regularLocalCoefficientPathRestriction F y (SimplexCategory.σ i) q :=
    regularLocalCoefficientPathIndexEquiv_restrict F y (SimplexCategory.σ i) s γ
  have hunit := congrArg (fun b : regularLocalCoefficientPathGenerators F y (n + 1) =>
    Limits.Sigma.ι (fun _ : regularLocalCoefficientPathGenerators F y (n + 1) => Z) b
      (ULift.up (1 : ℤ))) hp
  have hleft := (congrArg (fun b : SSet.localCoefficientObj L (n + 1) =>
    (regularLocalCoefficientIntegralBasisIso F y (n + 1)).hom b) hlocal).trans hgl
  have hright := (congrArg (fun b : A => D b) hgr).trans hd
  change (regularLocalCoefficientIntegralBasisIso F y (n + 1)).hom
      (SSet.localCoefficientDegeneracy L i
        (CategoryTheory.CategoryHomology.nervePullbackCoefficientι η L s
          (FreeAbelianGroup.of γ))) =
    D ((regularLocalCoefficientIntegralBasisIso F y (n)).hom
      (CategoryTheory.CategoryHomology.nervePullbackCoefficientι η L s
        (FreeAbelianGroup.of γ)))
  exact hleft.trans (hunit.trans hright.symm)

end SSet.KanComplex

namespace SSet.KanComplex

/-- Direct module restrictions use the actual native pullback generators and identity units. -/
noncomputable def nativeCoverPullbackPathModuleRestriction
    {X Y : SSet.{u}} (f : X ⟶ Y) (y : Y _⦋0⦌) {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    (∐ fun _ : nativeCoverPullbackSimplexPathGenerators f y n =>
      ModuleCat.of ℤ (ULift.{u} ℤ)) ⟶
    (∐ fun _ : nativeCoverPullbackSimplexPathGenerators f y m =>
      ModuleCat.of ℤ (ULift.{u} ℤ)) :=
  Limits.Sigma.map'
    (f := fun _ : nativeCoverPullbackSimplexPathGenerators f y m =>
      ModuleCat.of ℤ (ULift.{u} ℤ))
    (g := fun _ : nativeCoverPullbackSimplexPathGenerators f y n =>
      ModuleCat.of ℤ (ULift.{u} ℤ))
    (nativeCoverPullbackSimplexPathGeneratorsRestriction f y θ)
    (fun _ => 𝟙 (ModuleCat.of ℤ (ULift.{u} ℤ)))

/-- A direct native module restriction retains the unit of each restricted pair summand. -/
theorem nativeCoverPullbackPathModuleRestriction_ι
    {X Y : SSet.{u}} (f : X ⟶ Y) (y : Y _⦋0⦌) {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (p : nativeCoverPullbackSimplexPathGenerators f y n) :
    Limits.Sigma.ι (fun _ : nativeCoverPullbackSimplexPathGenerators f y n =>
        ModuleCat.of ℤ (ULift.{u} ℤ)) p ≫ nativeCoverPullbackPathModuleRestriction f y θ =
      Limits.Sigma.ι (fun _ : nativeCoverPullbackSimplexPathGenerators f y m =>
        ModuleCat.of ℤ (ULift.{u} ℤ))
        (nativeCoverPullbackSimplexPathGeneratorsRestriction f y θ p) := by
  change Limits.Sigma.ι (fun _ : nativeCoverPullbackSimplexPathGenerators f y n =>
      ModuleCat.of ℤ (ULift.{u} ℤ)) p ≫ Limits.Sigma.map'
    (f := fun _ : nativeCoverPullbackSimplexPathGenerators f y m =>
      ModuleCat.of ℤ (ULift.{u} ℤ))
    (g := fun _ : nativeCoverPullbackSimplexPathGenerators f y n =>
      ModuleCat.of ℤ (ULift.{u} ℤ))
    (nativeCoverPullbackSimplexPathGeneratorsRestriction f y θ)
    (fun _ => 𝟙 (ModuleCat.of ℤ (ULift.{u} ℤ))) = _
  exact (Limits.Sigma.ι_comp_map'
    (f := fun _ : nativeCoverPullbackSimplexPathGenerators f y m =>
      ModuleCat.of ℤ (ULift.{u} ℤ))
    (g := fun _ : nativeCoverPullbackSimplexPathGenerators f y n =>
      ModuleCat.of ℤ (ULift.{u} ℤ))
    (nativeCoverPullbackSimplexPathGeneratorsRestriction f y θ)
    (fun _ => 𝟙 (ModuleCat.of ℤ (ULift.{u} ℤ))) p).trans (Category.id_comp _)

/-- The computed path-index equivalence induces its constant-unit coproduct isomorphism. -/
noncomputable def regularLocalCoefficientPullbackPathModuleIndexIso
    {X Y : SSet.{u}} (f : X ⟶ Y) (y : Y _⦋0⦌) (n : ℕ) :
    (∐ fun _ : regularLocalCoefficientPathGenerators
      (SSet.mapFundamentalGroupoid f) (SSet.FundamentalGroupoid.mk y) n =>
        ModuleCat.of ℤ (ULift.{u} ℤ)) ≅
    (∐ fun _ : nativeCoverPullbackSimplexPathGenerators f y n =>
      ModuleCat.of ℤ (ULift.{u} ℤ)) :=
  Limits.Sigma.whiskerEquiv
    (f := fun _ : regularLocalCoefficientPathGenerators
      (SSet.mapFundamentalGroupoid f) (SSet.FundamentalGroupoid.mk y) n =>
        ModuleCat.of ℤ (ULift.{u} ℤ))
    (g := fun _ : nativeCoverPullbackSimplexPathGenerators f y n =>
      ModuleCat.of ℤ (ULift.{u} ℤ))
    (regularLocalCoefficientPullbackPathIndexEquiv f y n)
    (fun _ => Iso.refl (ModuleCat.of ℤ (ULift.{u} ℤ)))

/-- The constant-unit comparison sends each summand to its actual computed Q index. -/
theorem regularLocalCoefficientPullbackPathModuleIndexIso_ι_hom
    {X Y : SSet.{u}} (f : X ⟶ Y) (y : Y _⦋0⦌) (n : ℕ)
    (p : regularLocalCoefficientPathGenerators
      (SSet.mapFundamentalGroupoid f) (SSet.FundamentalGroupoid.mk y) n) :
    Limits.Sigma.ι (fun _ : regularLocalCoefficientPathGenerators
        (SSet.mapFundamentalGroupoid f) (SSet.FundamentalGroupoid.mk y) n =>
          ModuleCat.of ℤ (ULift.{u} ℤ)) p ≫
        (regularLocalCoefficientPullbackPathModuleIndexIso f y n).hom =
      Limits.Sigma.ι (fun _ : nativeCoverPullbackSimplexPathGenerators f y n =>
        ModuleCat.of ℤ (ULift.{u} ℤ)) (regularLocalCoefficientPullbackPathIndexEquiv f y n p) := by
  dsimp only [regularLocalCoefficientPullbackPathModuleIndexIso]
  rw [Limits.Sigma.whiskerEquiv_hom, Limits.Sigma.ι_comp_map']
  exact Category.id_comp _

/-- The whole Q module comparison preserves actual direct restrictions on both index systems. -/
theorem regularLocalCoefficientPullbackPathModuleIndexIso_restrict
    {X Y : SSet.{u}} (f : X ⟶ Y) (y : Y _⦋0⦌) {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    regularLocalCoefficientPathModuleRestriction
        (SSet.mapFundamentalGroupoid f) (SSet.FundamentalGroupoid.mk y) θ ≫
        (regularLocalCoefficientPullbackPathModuleIndexIso f y m).hom =
      (regularLocalCoefficientPullbackPathModuleIndexIso f y n).hom ≫
        nativeCoverPullbackPathModuleRestriction f y θ := by
  let F : SSet.FundamentalGroupoid X ⥤ SSet.FundamentalGroupoid Y :=
    SSet.mapFundamentalGroupoid f
  let b : SSet.FundamentalGroupoid Y := SSet.FundamentalGroupoid.mk y
  let Z : ModuleCat.{u} ℤ := ModuleCat.of ℤ (ULift.{u} ℤ)
  let Pn : Type u := regularLocalCoefficientPathGenerators F b n
  let Pm : Type u := regularLocalCoefficientPathGenerators F b m
  let Gn : Type u := nativeCoverPullbackSimplexPathGenerators f y n
  let Gm : Type u := nativeCoverPullbackSimplexPathGenerators f y m
  let D : (∐ fun _ : Pn => Z) ⟶ (∐ fun _ : Pm => Z) :=
    regularLocalCoefficientPathModuleRestriction F b θ
  let R : (∐ fun _ : Gn => Z) ⟶ (∐ fun _ : Gm => Z) :=
    nativeCoverPullbackPathModuleRestriction f y θ
  let Wn : (∐ fun _ : Pn => Z) ≅ (∐ fun _ : Gn => Z) :=
    regularLocalCoefficientPullbackPathModuleIndexIso f y n
  let Wm : (∐ fun _ : Pm => Z) ≅ (∐ fun _ : Gm => Z) :=
    regularLocalCoefficientPullbackPathModuleIndexIso f y m
  change D ≫ Wm.hom = Wn.hom ≫ R
  refine Limits.Sigma.hom_ext _ _ ?_
  intro p
  have hLp : (Limits.Sigma.ι (fun _ : Pn => Z) p ≫ D) ≫ Wm.hom =
      Limits.Sigma.ι (fun _ : Pm => Z) (regularLocalCoefficientPathRestriction F b θ p) ≫
        Wm.hom :=
    congrArg (fun h : Z ⟶ (∐ fun _ : Pm => Z) => h ≫ Wm.hom)
      (regularLocalCoefficientPathModuleRestriction_ι F b θ p)
  have hl : Limits.Sigma.ι (fun _ : Pn => Z) p ≫ D ≫ Wm.hom =
      Limits.Sigma.ι (fun _ : Gm => Z)
        (regularLocalCoefficientPullbackPathIndexEquiv f y m
          (regularLocalCoefficientPathRestriction F b θ p)) :=
    (Category.assoc (Limits.Sigma.ι (fun _ : Pn => Z) p) D Wm.hom).symm.trans
      (hLp.trans (regularLocalCoefficientPullbackPathModuleIndexIso_ι_hom f y m
        (regularLocalCoefficientPathRestriction F b θ p)))
  have hRp : (Limits.Sigma.ι (fun _ : Pn => Z) p ≫ Wn.hom) ≫ R =
      Limits.Sigma.ι (fun _ : Gn => Z) (regularLocalCoefficientPullbackPathIndexEquiv f y n p) ≫
        R :=
    congrArg (fun h : Z ⟶ (∐ fun _ : Gn => Z) => h ≫ R)
      (regularLocalCoefficientPullbackPathModuleIndexIso_ι_hom f y n p)
  have hr : Limits.Sigma.ι (fun _ : Pn => Z) p ≫ Wn.hom ≫ R =
      Limits.Sigma.ι (fun _ : Gm => Z)
        (nativeCoverPullbackSimplexPathGeneratorsRestriction f y θ
          (regularLocalCoefficientPullbackPathIndexEquiv f y n p)) :=
    (Category.assoc (Limits.Sigma.ι (fun _ : Pn => Z) p) Wn.hom R).symm.trans
      (hRp.trans (nativeCoverPullbackPathModuleRestriction_ι f y θ
        (regularLocalCoefficientPullbackPathIndexEquiv f y n p)))
  have hp : regularLocalCoefficientPullbackPathIndexEquiv f y m
        (regularLocalCoefficientPathRestriction F b θ p) =
      nativeCoverPullbackSimplexPathGeneratorsRestriction f y θ
        (regularLocalCoefficientPullbackPathIndexEquiv f y n p) :=
    regularLocalCoefficientPullbackPathIndexEquiv_restrict f y θ p
  have hι := congrArg (fun q : Gm => Limits.Sigma.ι (fun _ : Gm => Z) q) hp
  exact hl.trans (hι.trans hr.symm)

/-- The actual original degree comparison preserves every native pullback module face. -/
theorem regularLocalCoefficientPullbackIntegralBasisIso_face
    {X Y : SSet.{u}} (f : X ⟶ Y) (y : Y _⦋0⦌) {n : ℕ} (i : Fin (n + 2)) :
    SSet.localCoefficientFace ((SSet.mapFundamentalGroupoid f) ⋙
        CategoryTheory.regularPathModuleCoefficientFunctor (SSet.FundamentalGroupoid.mk y)) i ≫
        (regularLocalCoefficientPullbackIntegralBasisIso f y n).hom =
      (regularLocalCoefficientPullbackIntegralBasisIso f y (n + 1)).hom ≫
        nativeCoverPullbackPathModuleRestriction f y (SimplexCategory.δ i) := by
  let F : SSet.FundamentalGroupoid X ⥤ SSet.FundamentalGroupoid Y :=
    SSet.mapFundamentalGroupoid f
  let b : SSet.FundamentalGroupoid Y := SSet.FundamentalGroupoid.mk y
  let L := F ⋙ CategoryTheory.regularPathModuleCoefficientFunctor b
  let Z : ModuleCat.{u} ℤ := ModuleCat.of ℤ (ULift.{u} ℤ)
  let S : ModuleCat.{u} ℤ := SSet.localCoefficientObj L (n + 1)
  let T : ModuleCat.{u} ℤ := SSet.localCoefficientObj L n
  let P : ModuleCat.{u} ℤ := ∐ fun _ : regularLocalCoefficientPathGenerators F b (n + 1) => Z
  let Q : ModuleCat.{u} ℤ := ∐ fun _ : regularLocalCoefficientPathGenerators F b n => Z
  let U : ModuleCat.{u} ℤ := ∐ fun _ : nativeCoverPullbackSimplexPathGenerators f y (n + 1) => Z
  let V : ModuleCat.{u} ℤ := ∐ fun _ : nativeCoverPullbackSimplexPathGenerators f y n => Z
  let h : S ⟶ T := SSet.localCoefficientFace L i
  let a : S ⟶ P := (regularLocalCoefficientIntegralBasisIso F b (n + 1)).hom
  let c : T ⟶ Q := (regularLocalCoefficientIntegralBasisIso F b n).hom
  let q0 : P ⟶ U := (regularLocalCoefficientPullbackPathModuleIndexIso f y (n + 1)).hom
  let q1 : Q ⟶ V := (regularLocalCoefficientPullbackPathModuleIndexIso f y n).hom
  let d : P ⟶ Q := regularLocalCoefficientPathModuleRestriction F b (SimplexCategory.δ i)
  let r : U ⟶ V := nativeCoverPullbackPathModuleRestriction f y (SimplexCategory.δ i)
  change h ≫ (c ≫ q1) = (a ≫ q0) ≫ r
  have hb : h ≫ c = a ≫ d := regularLocalCoefficientIntegralBasisIso_face F b i
  have hq : d ≫ q1 = q0 ≫ r :=
    regularLocalCoefficientPullbackPathModuleIndexIso_restrict f y (SimplexCategory.δ i)
  have h2 : (h ≫ c) ≫ q1 = (a ≫ d) ≫ q1 :=
    congrArg (fun k : S ⟶ Q => k ≫ q1) hb
  have h4 : a ≫ (d ≫ q1) = a ≫ (q0 ≫ r) :=
    congrArg (fun k : P ⟶ V => a ≫ k) hq
  exact (Category.assoc h c q1).symm.trans
    (h2.trans ((Category.assoc a d q1).trans
      (h4.trans (Category.assoc a q0 r).symm)))

/-- The actual original degree comparison preserves every native pullback module degeneracy. -/
theorem regularLocalCoefficientPullbackIntegralBasisIso_degeneracy
    {X Y : SSet.{u}} (f : X ⟶ Y) (y : Y _⦋0⦌) {n : ℕ} (i : Fin (n + 1)) :
    SSet.localCoefficientDegeneracy ((SSet.mapFundamentalGroupoid f) ⋙
        CategoryTheory.regularPathModuleCoefficientFunctor (SSet.FundamentalGroupoid.mk y)) i ≫
        (regularLocalCoefficientPullbackIntegralBasisIso f y (n + 1)).hom =
      (regularLocalCoefficientPullbackIntegralBasisIso f y n).hom ≫
        nativeCoverPullbackPathModuleRestriction f y (SimplexCategory.σ i) := by
  let F : SSet.FundamentalGroupoid X ⥤ SSet.FundamentalGroupoid Y :=
    SSet.mapFundamentalGroupoid f
  let b : SSet.FundamentalGroupoid Y := SSet.FundamentalGroupoid.mk y
  let L := F ⋙ CategoryTheory.regularPathModuleCoefficientFunctor b
  let Z : ModuleCat.{u} ℤ := ModuleCat.of ℤ (ULift.{u} ℤ)
  let S : ModuleCat.{u} ℤ := SSet.localCoefficientObj L n
  let T : ModuleCat.{u} ℤ := SSet.localCoefficientObj L (n + 1)
  let P : ModuleCat.{u} ℤ := ∐ fun _ : regularLocalCoefficientPathGenerators F b n => Z
  let Q : ModuleCat.{u} ℤ := ∐ fun _ : regularLocalCoefficientPathGenerators F b (n + 1) => Z
  let U : ModuleCat.{u} ℤ := ∐ fun _ : nativeCoverPullbackSimplexPathGenerators f y n => Z
  let V : ModuleCat.{u} ℤ := ∐ fun _ : nativeCoverPullbackSimplexPathGenerators f y (n + 1) => Z
  let h : S ⟶ T := SSet.localCoefficientDegeneracy L i
  let a : S ⟶ P := (regularLocalCoefficientIntegralBasisIso F b n).hom
  let c : T ⟶ Q := (regularLocalCoefficientIntegralBasisIso F b (n + 1)).hom
  let q0 : P ⟶ U := (regularLocalCoefficientPullbackPathModuleIndexIso f y n).hom
  let q1 : Q ⟶ V := (regularLocalCoefficientPullbackPathModuleIndexIso f y (n + 1)).hom
  let d : P ⟶ Q := regularLocalCoefficientPathModuleRestriction F b (SimplexCategory.σ i)
  let r : U ⟶ V := nativeCoverPullbackPathModuleRestriction f y (SimplexCategory.σ i)
  change h ≫ (c ≫ q1) = (a ≫ q0) ≫ r
  have hb : h ≫ c = a ≫ d := regularLocalCoefficientIntegralBasisIso_degeneracy F b i
  have hq : d ≫ q1 = q0 ≫ r :=
    regularLocalCoefficientPullbackPathModuleIndexIso_restrict f y (SimplexCategory.σ i)
  have h2 : (h ≫ c) ≫ q1 = (a ≫ d) ≫ q1 :=
    congrArg (fun k : S ⟶ Q => k ≫ q1) hb
  have h4 : a ≫ (d ≫ q1) = a ≫ (q0 ≫ r) :=
    congrArg (fun k : P ⟶ V => a ≫ k) hq
  exact (Category.assoc h c q1).symm.trans
    (h2.trans ((Category.assoc a d q1).trans
      (h4.trans (Category.assoc a q0 r).symm)))

end SSet.KanComplex

namespace SSet.KanComplex

/-- Original simplices paired with paths from the fixed original cover point. -/
def nativeCoverSimplexPathGenerators (X : SSet.{u}) (x : X _⦋0⦌) (n : ℕ) : Type u :=
  Σ σ : (Δ[n] : SSet.{u}) ⟶ X,
    (SSet.FundamentalGroupoid.mk x ⟶ SSet.FundamentalGroupoid.mk
      ((SSet.yonedaEquiv (X := X) (n := ⦋0⦌))
        ((SSet.yonedaEquiv.symm (SSet.stdSimplex.obj₀Equiv.symm
          (0 : Fin (n + 1))) : (Δ[0] : SSet.{u}) ⟶ Δ[n]) ≫ σ)))

/-- The actual lift-coordinate inverse and Yoneda give the original covering simplices. -/
noncomputable def nativeCoverSimplexPathGeneratorsEquiv
    (X : SSet.{u}) (x : X _⦋0⦌) (n : ℕ) :
    nativeCoverSimplexPathGenerators X x n ≃ (nativeCover X x) _⦋n⦌ :=
  (Equiv.sigmaCongrRight (fun σ : (Δ[n] : SSet.{u}) ⟶ X =>
      (nativeCoverSimplexFiberPathEquiv (X := X) (x := x) σ).symm)).trans
    ((Equiv.sigmaFiberEquiv (fun L : (Δ[n] : SSet.{u}) ⟶ nativeCover X x =>
        L ≫ nativeCoverProjection X x)).trans
      (SSet.yonedaEquiv (X := nativeCover X x) (n := ⦋n⦌)))

/-- Forward generators use the original canonical lifted simplex. -/
theorem nativeCoverSimplexPathGeneratorsEquiv_apply
    (X : SSet.{u}) (x : X _⦋0⦌) (n : ℕ)
    (σ : (Δ[n] : SSet.{u}) ⟶ X)
    (γ : SSet.FundamentalGroupoid.mk x ⟶ SSet.FundamentalGroupoid.mk
      ((SSet.yonedaEquiv (X := X) (n := ⦋0⦌))
        ((SSet.yonedaEquiv.symm (SSet.stdSimplex.obj₀Equiv.symm
          (0 : Fin (n + 1))) : (Δ[0] : SSet.{u}) ⟶ Δ[n]) ≫ σ))) :
    nativeCoverSimplexPathGeneratorsEquiv X x n ⟨σ, γ⟩ =
      (SSet.yonedaEquiv (X := nativeCover X x) (n := ⦋n⦌))
        ((nativeCoverSimplexFiberPathEquiv (X := X) (x := x) σ).symm γ).val := by
  dsimp only [nativeCoverSimplexPathGeneratorsEquiv, Equiv.trans, Equiv.sigmaCongrRight,
    Equiv.sigmaFiberEquiv] ; rfl

/-- The inverse records the actual first projection and original path coordinate. -/
theorem nativeCoverSimplexPathGeneratorsEquiv_symm_apply
    (X : SSet.{u}) (x : X _⦋0⦌) (n : ℕ) (s : (nativeCover X x) _⦋n⦌) :
    (nativeCoverSimplexPathGeneratorsEquiv X x n).symm s =
      ⟨((SSet.yonedaEquiv (X := nativeCover X x) (n := ⦋n⦌)).symm s) ≫
          nativeCoverProjection X x,
        nativeCoverSimplexFiberPathEquiv
          (((SSet.yonedaEquiv (X := nativeCover X x) (n := ⦋n⦌)).symm s) ≫
            nativeCoverProjection X x)
          ⟨(SSet.yonedaEquiv (X := nativeCover X x) (n := ⦋n⦌)).symm s, rfl⟩⟩ := by
  dsimp only [nativeCoverSimplexPathGeneratorsEquiv, Equiv.trans, Equiv.sigmaCongrRight,
    Equiv.sigmaFiberEquiv] ; rfl

/-- The covering projection of a generator is the original base simplex. -/
theorem nativeCoverSimplexPathGeneratorsEquiv_projection
    (X : SSet.{u}) (x : X _⦋0⦌) (n : ℕ)
    (g : nativeCoverSimplexPathGenerators X x n) :
    (nativeCoverProjection X x).app (Opposite.op ⦋n⦌)
        (nativeCoverSimplexPathGeneratorsEquiv X x n g) =
      (SSet.yonedaEquiv (X := X) (n := ⦋n⦌)) g.1 := by
  rcases g with ⟨σ, γ⟩
  let L := (nativeCoverSimplexFiberPathEquiv (X := X) (x := x) σ).symm γ
  have hL : L.val ≫ nativeCoverProjection X x = σ := L.property
  exact (congrArg (fun s : (nativeCover X x) _⦋n⦌ =>
      (nativeCoverProjection X x).app (Opposite.op ⦋n⦌) s)
    (nativeCoverSimplexPathGeneratorsEquiv_apply X x n σ γ)).trans
      ((SSet.yonedaEquiv_comp L.val (nativeCoverProjection X x)).symm.trans
        (congrArg (SSet.yonedaEquiv (X := X) (n := ⦋n⦌)) hL))

/-- The constructed inverse recovers every original simplex/path pair. -/
theorem nativeCoverSimplexPathGeneratorsEquiv_left_inv
    (X : SSet.{u}) (x : X _⦋0⦌) (n : ℕ) (g : nativeCoverSimplexPathGenerators X x n) :
    (nativeCoverSimplexPathGeneratorsEquiv X x n).symm
      (nativeCoverSimplexPathGeneratorsEquiv X x n g) = g :=
  (nativeCoverSimplexPathGeneratorsEquiv X x n).symm_apply_apply g

/-- The constructed forward map recovers every original covering simplex. -/
theorem nativeCoverSimplexPathGeneratorsEquiv_right_inv
    (X : SSet.{u}) (x : X _⦋0⦌) (n : ℕ) (s : (nativeCover X x) _⦋n⦌) :
    nativeCoverSimplexPathGeneratorsEquiv X x n
      ((nativeCoverSimplexPathGeneratorsEquiv X x n).symm s) = s :=
  (nativeCoverSimplexPathGeneratorsEquiv X x n).apply_symm_apply s

end SSet.KanComplex

namespace SSet.KanComplex

/-- Restrict the original simplex and postcompose its path with the computed base transport. -/
def nativeCoverSimplexPathGeneratorsRestriction
    (X : SSet.{u}) (x : X _⦋0⦌) {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    nativeCoverSimplexPathGenerators X x n → nativeCoverSimplexPathGenerators X x m :=
  fun g => ⟨SSet.stdSimplex.map θ ≫ g.1,
    g.2 ≫ nativeCoverSimplexPathTransport g.1 θ⟩

/-- The direct path restriction agrees with restriction of the actual lifted simplex. -/
theorem nativeCoverSimplexPathGeneratorsEquiv_restrict
    (X : SSet.{u}) (x : X _⦋0⦌) {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (g : nativeCoverSimplexPathGenerators X x n) :
    nativeCoverSimplexPathGeneratorsEquiv X x m
        (nativeCoverSimplexPathGeneratorsRestriction X x θ g) =
      (nativeCover X x).map θ.op (nativeCoverSimplexPathGeneratorsEquiv X x n g) := by
  rcases g with ⟨σ, γ⟩
  let P : SSet.{u} := nativeCover X x
  let p : P ⟶ X := nativeCoverProjection X x
  let σ' : (Δ[m] : SSet.{u}) ⟶ X := SSet.stdSimplex.map θ ≫ σ
  let L : {L : (Δ[n] : SSet.{u}) ⟶ P // L ≫ p = σ} :=
    (nativeCoverSimplexFiberPathEquiv (X := X) (x := x) σ).symm γ
  let L' : {L : (Δ[m] : SSet.{u}) ⟶ P // L ≫ p = σ'} :=
    ⟨SSet.stdSimplex.map θ ≫ L.val, (Category.assoc _ _ _).trans
      (congrArg (fun f : (Δ[n] : SSet.{u}) ⟶ X => SSet.stdSimplex.map θ ≫ f)
        L.property)⟩
  have hc : nativeCoverSimplexFiberPathEquiv σ' L' =
      γ ≫ nativeCoverSimplexPathTransport σ θ :=
    (nativeCoverSimplexFiberPathEquiv_restrict σ θ L).trans
      (congrArg (fun δ => δ ≫ nativeCoverSimplexPathTransport σ θ)
        ((nativeCoverSimplexFiberPathEquiv (X := X) (x := x) σ).apply_symm_apply γ))
  have hL : (nativeCoverSimplexFiberPathEquiv (X := X) (x := x) σ').symm
      (γ ≫ nativeCoverSimplexPathTransport σ θ) = L' :=
    (nativeCoverSimplexFiberPathEquiv (X := X) (x := x) σ').symm_apply_eq.mpr hc.symm
  exact (nativeCoverSimplexPathGeneratorsEquiv_apply X x m σ'
      (γ ≫ nativeCoverSimplexPathTransport σ θ)).trans
    ((congrArg (fun K : {K : (Δ[m] : SSet.{u}) ⟶ P // K ≫ p = σ'} =>
        (SSet.yonedaEquiv (X := P) (n := ⦋m⦌)) K.val) hL).trans
      ((SSet.yonedaEquiv_naturality θ L.val).symm.trans
        (congrArg (fun s : P _⦋n⦌ => P.map θ.op s)
          (nativeCoverSimplexPathGeneratorsEquiv_apply X x n σ γ).symm)))

/-- The independently specified restriction preserves identity. -/
theorem nativeCoverSimplexPathGeneratorsRestriction_id
    (X : SSet.{u}) (x : X _⦋0⦌) (n : ℕ)
    (g : nativeCoverSimplexPathGenerators X x n) :
    nativeCoverSimplexPathGeneratorsRestriction X x (𝟙 ⦋n⦌) g = g := by
  apply (nativeCoverSimplexPathGeneratorsEquiv X x n).injective
  exact (nativeCoverSimplexPathGeneratorsEquiv_restrict X x (𝟙 ⦋n⦌) g).trans
    (congrArg (fun f : (nativeCover X x) _⦋n⦌ ⟶ (nativeCover X x) _⦋n⦌ =>
        f (nativeCoverSimplexPathGeneratorsEquiv X x n g))
      ((nativeCover X x).map_id (Opposite.op ⦋n⦌)))

/-- Composing direct simplex/path restrictions equals the direct composite restriction. -/
theorem nativeCoverSimplexPathGeneratorsRestriction_comp
    (X : SSet.{u}) (x : X _⦋0⦌) {l m n : ℕ}
    (θ : ⦋m⦌ ⟶ ⦋n⦌) (ρ : ⦋l⦌ ⟶ ⦋m⦌)
    (g : nativeCoverSimplexPathGenerators X x n) :
    nativeCoverSimplexPathGeneratorsRestriction X x ρ
        (nativeCoverSimplexPathGeneratorsRestriction X x θ g) =
      nativeCoverSimplexPathGeneratorsRestriction X x (ρ ≫ θ) g := by
  apply (nativeCoverSimplexPathGeneratorsEquiv X x l).injective
  have hP : (nativeCover X x).map (ρ ≫ θ).op
        (nativeCoverSimplexPathGeneratorsEquiv X x n g) =
      (nativeCover X x).map ρ.op ((nativeCover X x).map θ.op
        (nativeCoverSimplexPathGeneratorsEquiv X x n g)) :=
    congrArg (fun f : (nativeCover X x) _⦋n⦌ ⟶ (nativeCover X x) _⦋l⦌ =>
      f (nativeCoverSimplexPathGeneratorsEquiv X x n g))
      ((nativeCover X x).map_comp θ.op ρ.op)
  exact (nativeCoverSimplexPathGeneratorsEquiv_restrict X x ρ
      (nativeCoverSimplexPathGeneratorsRestriction X x θ g)).trans
    ((congrArg (fun s : (nativeCover X x) _⦋m⦌ => (nativeCover X x).map ρ.op s)
      (nativeCoverSimplexPathGeneratorsEquiv_restrict X x θ g)).trans
      (hP.symm.trans (nativeCoverSimplexPathGeneratorsEquiv_restrict X x (ρ ≫ θ) g).symm))

/-- The original simplex/path generators with their direct restriction maps. -/
def nativeCoverSimplexPathGeneratorSSet (X : SSet.{u}) (x : X _⦋0⦌) : SSet.{u} where
  obj d := nativeCoverSimplexPathGenerators X x d.unop.len
  map α := TypeCat.ofHom (nativeCoverSimplexPathGeneratorsRestriction X x α.unop)
  map_id d := by
    apply ConcreteCategory.ext_apply
    intro g
    change nativeCoverSimplexPathGeneratorsRestriction X x (𝟙 ⦋d.unop.len⦌) g = g
    exact nativeCoverSimplexPathGeneratorsRestriction_id X x d.unop.len g
  map_comp α β := by
    apply ConcreteCategory.ext_apply
    intro g
    change nativeCoverSimplexPathGeneratorsRestriction X x (β.unop ≫ α.unop) g =
      nativeCoverSimplexPathGeneratorsRestriction X x β.unop
        (nativeCoverSimplexPathGeneratorsRestriction X x α.unop g)
    exact (nativeCoverSimplexPathGeneratorsRestriction_comp X x α.unop β.unop g).symm

/-- The constructed component equivalences form a natural isomorphism to the original cover. -/
noncomputable def nativeCoverSimplexPathGeneratorIso (X : SSet.{u}) (x : X _⦋0⦌) :
    nativeCoverSimplexPathGeneratorSSet X x ≅ nativeCover X x :=
  NatIso.ofComponents
    (F := nativeCoverSimplexPathGeneratorSSet X x) (G := nativeCover X x)
    (fun d => (nativeCoverSimplexPathGeneratorsEquiv X x d.unop.len).toIso) (by
      intro a b α
      apply ConcreteCategory.ext_apply
      intro g
      change nativeCoverSimplexPathGeneratorsEquiv X x b.unop.len
          (nativeCoverSimplexPathGeneratorsRestriction X x α.unop g) =
        (nativeCover X x).map α (nativeCoverSimplexPathGeneratorsEquiv X x a.unop.len g)
      exact nativeCoverSimplexPathGeneratorsEquiv_restrict X x α.unop g)

/-- The natural comparison has the original constructed lift-coordinate forward map. -/
theorem nativeCoverSimplexPathGeneratorIso_hom_app
    (X : SSet.{u}) (x : X _⦋0⦌) (n : ℕ)
    (g : nativeCoverSimplexPathGenerators X x n) :
    (nativeCoverSimplexPathGeneratorIso X x).hom.app (Opposite.op ⦋n⦌) g =
      nativeCoverSimplexPathGeneratorsEquiv X x n g := by
  dsimp only [nativeCoverSimplexPathGeneratorIso, NatIso.ofComponents, Equiv.toIso] ; rfl

end SSet.KanComplex

universe w

namespace SSet.KanComplex

variable {C : Type w} [Category.{v} C] [HasCoproducts.{u} C] [Preadditive C]

/-- Regular coefficient chains use original simplex/path pairs and their direct restrictions. -/
noncomputable def nativeRegularCoefficientChainComplex
    (X : SSet.{u}) (x : X _⦋0⦌) (R : C) : ChainComplex C ℕ :=
  (nativeCoverSimplexPathGeneratorSSet X x).chainComplex R

/-- The summand corresponding to one original simplex/path pair in the independent complex. -/
noncomputable def nativeRegularCoefficientChainGenerator
    (X : SSet.{u}) (x : X _⦋0⦌) (R : C) {n : ℕ}
    (g : nativeCoverSimplexPathGenerators X x n) :
    R ⟶ (nativeRegularCoefficientChainComplex X x R).X n :=
  (nativeCoverSimplexPathGeneratorSSet X x).ιChainComplex (R := R) g

/-- The canonical natural cover comparison induces the actual chain isomorphism. -/
noncomputable def nativeRegularCoefficientChainCoverIso
    (X : SSet.{u}) (x : X _⦋0⦌) (R : C) :
    nativeRegularCoefficientChainComplex X x R ≅ (nativeCover X x).chainComplex R :=
  ((SSet.chainComplexFunctor C).obj R).mapIso (nativeCoverSimplexPathGeneratorIso X x)

/-- The chain comparison sends each original pair to its actual lifted covering simplex. -/
theorem nativeRegularCoefficientChainCoverIso_on_generator
    (X : SSet.{u}) (x : X _⦋0⦌) (R : C) {n : ℕ}
    (g : nativeCoverSimplexPathGenerators X x n) :
    nativeRegularCoefficientChainGenerator X x R g ≫
        (nativeRegularCoefficientChainCoverIso X x R).hom.f n =
      (nativeCover X x).ιChainComplex (R := R)
        (nativeCoverSimplexPathGeneratorsEquiv X x n g) := by
  change (nativeCoverSimplexPathGeneratorSSet X x).ιChainComplex (R := R) g ≫
      (SSet.chainComplexMap (nativeCoverSimplexPathGeneratorIso X x).hom R).f n = _
  exact (SSet.ι_chainComplexMap_f
      (X := nativeCoverSimplexPathGeneratorSSet X x) (Y := nativeCover X x)
      (f := (nativeCoverSimplexPathGeneratorIso X x).hom) (R := R) (n := n)
      (show (nativeCoverSimplexPathGeneratorSSet X x) _⦋n⦌ from g)).trans
    (congrArg (fun s : (nativeCover X x) _⦋n⦌ =>
      (nativeCover X x).ιChainComplex (R := R) (n := n) s)
      (nativeCoverSimplexPathGeneratorIso_hom_app X x n g))

/-- The independent differential is the alternating sum of actual simplex/path restrictions. -/
theorem nativeRegularCoefficientChainComplex_d_on_generator
    (X : SSet.{u}) (x : X _⦋0⦌) (R : C) {n : ℕ}
    (g : nativeCoverSimplexPathGenerators X x (n + 1)) :
    nativeRegularCoefficientChainGenerator X x R g ≫
        (nativeRegularCoefficientChainComplex X x R).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        nativeRegularCoefficientChainGenerator X x R
          (nativeCoverSimplexPathGeneratorsRestriction X x (SimplexCategory.δ i) g) := by
  change (nativeCoverSimplexPathGeneratorSSet X x).ιChainComplex (R := R) g ≫
      ((nativeCoverSimplexPathGeneratorSSet X x).chainComplex R).d (n + 1) n =
    ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
      (nativeCoverSimplexPathGeneratorSSet X x).ιChainComplex (R := R)
        ((nativeCoverSimplexPathGeneratorSSet X x).δ i g)
  exact (nativeCoverSimplexPathGeneratorSSet X x).ιChainComplex_d R g

end SSet.KanComplex

namespace SSet.KanComplex

/-- Map the original source simplex through f, leaving its arbitrary-target-point path unchanged. -/
def nativeCoverPullbackSimplexPathGeneratorsTargetMap
    {X Y : SSet.{u}} (f : X ⟶ Y) (y : Y _⦋0⦌) (n : ℕ) :
    nativeCoverPullbackSimplexPathGenerators f y n → nativeCoverSimplexPathGenerators Y y n :=
  fun g => ⟨g.1 ≫ f, g.2⟩

/-- The direct generator map compares with the actual second projection of the literal pullback. -/
theorem nativeCoverPullbackSimplexPathGeneratorsTargetMap_equiv
    {X Y : SSet.{u}} (f : X ⟶ Y) (y : Y _⦋0⦌) (n : ℕ)
    (g : nativeCoverPullbackSimplexPathGenerators f y n) :
    nativeCoverSimplexPathGeneratorsEquiv Y y n
        (nativeCoverPullbackSimplexPathGeneratorsTargetMap f y n g) =
      (pullback.snd f (nativeCoverProjection Y y)).app (Opposite.op ⦋n⦌)
        (nativeCoverPullbackSimplexPathGeneratorsEquiv f y n g) := by
  rcases g with ⟨σ, γ⟩
  let P : SSet.{u} := nativeCover Y y
  let W : SSet.{u} := pullback f (nativeCoverProjection Y y)
  let r : W ⟶ P := pullback.snd f (nativeCoverProjection Y y)
  let L : {L : (Δ[n] : SSet.{u}) ⟶ W //
      L ≫ pullback.fst f (nativeCoverProjection Y y) = σ} :=
    (nativeCoverPullbackSimplexPathEquiv f y σ).symm γ
  let T : {T : (Δ[n] : SSet.{u}) ⟶ P // T ≫ nativeCoverProjection Y y = σ ≫ f} :=
    nativeCoverPullbackSimplexFiberEquiv f y σ L
  have hc : nativeCoverSimplexFiberPathEquiv (σ ≫ f) T = γ :=
    (nativeCoverPullbackSimplexPathEquiv f y σ).apply_symm_apply γ
  have hT : (nativeCoverSimplexFiberPathEquiv (X := Y) (x := y) (σ ≫ f)).symm γ = T :=
    (nativeCoverSimplexFiberPathEquiv (X := Y) (x := y) (σ ≫ f)).symm_apply_eq.mpr hc.symm
  exact (nativeCoverSimplexPathGeneratorsEquiv_apply Y y n (σ ≫ f) γ).trans
    ((congrArg (fun K : {K : (Δ[n] : SSet.{u}) ⟶ P // K ≫ nativeCoverProjection Y y = σ ≫ f} =>
      (SSet.yonedaEquiv (X := P) (n := ⦋n⦌)) K.val) hT).trans
      ((congrArg (SSet.yonedaEquiv (X := P) (n := ⦋n⦌))
        (nativeCoverPullbackSimplexFiberEquiv_apply f y σ L)).trans
        ((SSet.yonedaEquiv_comp L.val r).trans
          (congrArg (fun s : W _⦋n⦌ => r.app (Opposite.op ⦋n⦌) s)
            (nativeCoverPullbackSimplexPathGeneratorsEquiv_apply f y n ⟨σ, γ⟩).symm))))

private theorem nativeGenerator_baseCast
    {Y : SSet.{u}} (y : Y _⦋0⦌) {n : ℕ}
    (g : nativeCoverSimplexPathGenerators Y y n) (τ : (Δ[n] : SSet.{u}) ⟶ Y) (h : g.1 = τ) :
    let α : (Δ[0] : SSet.{u}) ⟶ Δ[n] := SSet.yonedaEquiv.symm
      (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1)))
    (⟨τ, g.2 ≫ eqToHom (congrArg (fun ζ : (Δ[n] : SSet.{u}) ⟶ Y =>
      SSet.FundamentalGroupoid.mk ((SSet.yonedaEquiv (n := ⦋0⦌)) (α ≫ ζ))) h)⟩ :
      nativeCoverSimplexPathGenerators Y y n) = g := by
  rcases g with ⟨σ, γ⟩
  subst τ
  change (⟨σ, γ ≫ 𝟙 _⟩ : nativeCoverSimplexPathGenerators Y y n) = ⟨σ, γ⟩
  exact congrArg (fun δ : SSet.FundamentalGroupoid.mk y ⟶ SSet.FundamentalGroupoid.mk
      ((SSet.yonedaEquiv (n := ⦋0⦌))
        ((SSet.yonedaEquiv.symm (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1))) :
          (Δ[0] : SSet.{u}) ⟶ Δ[n]) ≫ σ)) =>
    (⟨σ, δ⟩ : nativeCoverSimplexPathGenerators Y y n)) (Category.comp_id γ)

/-- The original-f map commutes with the independently specified restrictions and their endpoint
casts. -/
theorem nativeCoverPullbackSimplexPathGeneratorsTargetMap_restrict
    {X Y : SSet.{u}} (f : X ⟶ Y) (y : Y _⦋0⦌) {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (g : nativeCoverPullbackSimplexPathGenerators f y n) :
    nativeCoverPullbackSimplexPathGeneratorsTargetMap f y m
        (nativeCoverPullbackSimplexPathGeneratorsRestriction f y θ g) =
      nativeCoverSimplexPathGeneratorsRestriction Y y θ
        (nativeCoverPullbackSimplexPathGeneratorsTargetMap f y n g) := by
  rcases g with ⟨σ, γ⟩
  let a : (Δ[m] : SSet.{u}) ⟶ Δ[n] := SSet.stdSimplex.map θ
  let σ' : (Δ[m] : SSet.{u}) ⟶ Y := a ≫ (σ ≫ f)
  let τ' : (Δ[m] : SSet.{u}) ⟶ Y := (a ≫ σ) ≫ f
  let h : σ' = τ' := (Category.assoc a σ f).symm
  let α : (Δ[0] : SSet.{u}) ⟶ Δ[m] := SSet.yonedaEquiv.symm
    (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin (m + 1)))
  let κ := congrArg (fun ζ : (Δ[m] : SSet.{u}) ⟶ Y => SSet.FundamentalGroupoid.mk
    ((SSet.yonedaEquiv (n := ⦋0⦌)) (α ≫ ζ))) h
  change (⟨τ', γ ≫ (nativeCoverSimplexPathTransport (σ ≫ f) θ ≫ eqToHom κ)⟩ :
    nativeCoverSimplexPathGenerators Y y m) = ⟨σ', γ ≫ nativeCoverSimplexPathTransport (σ ≫ f) θ⟩
  exact (congrArg (fun δ : SSet.FundamentalGroupoid.mk y ⟶ SSet.FundamentalGroupoid.mk
      ((SSet.yonedaEquiv (n := ⦋0⦌)) (α ≫ τ')) =>
        (⟨τ', δ⟩ : nativeCoverSimplexPathGenerators Y y m))
    (Category.assoc γ (nativeCoverSimplexPathTransport (σ ≫ f) θ) (eqToHom κ)).symm).trans
    (nativeGenerator_baseCast y ⟨σ', γ ≫ nativeCoverSimplexPathTransport (σ ≫ f) θ⟩ τ' h)

end SSet.KanComplex

namespace SSet.KanComplex

/-- The original-f component map bundles using its proved direct restriction compatibility. -/
def nativeCoverPullbackSimplexPathGeneratorTargetMap
    {X Y : SSet.{u}} (f : X ⟶ Y) (y : Y _⦋0⦌) :
    nativeCoverPullbackSimplexPathGeneratorSSet f y ⟶
      nativeCoverSimplexPathGeneratorSSet Y y where
  app d := TypeCat.ofHom
    (nativeCoverPullbackSimplexPathGeneratorsTargetMap f y d.unop.len)
  naturality a b α := by
    apply ConcreteCategory.ext_apply
    intro g
    change nativeCoverPullbackSimplexPathGeneratorsTargetMap f y b.unop.len
        (nativeCoverPullbackSimplexPathGeneratorsRestriction f y α.unop g) =
      nativeCoverSimplexPathGeneratorsRestriction Y y α.unop
        (nativeCoverPullbackSimplexPathGeneratorsTargetMap f y a.unop.len g)
    exact nativeCoverPullbackSimplexPathGeneratorsTargetMap_restrict f y α.unop g

/-- Every degree component retains the original simplex and unchanged target path. -/
theorem nativeCoverPullbackSimplexPathGeneratorTargetMap_app
    {X Y : SSet.{u}} (f : X ⟶ Y) (y : Y _⦋0⦌) (n : ℕ)
    (g : nativeCoverPullbackSimplexPathGenerators f y n) :
    (nativeCoverPullbackSimplexPathGeneratorTargetMap f y).app (Opposite.op ⦋n⦌) g =
      nativeCoverPullbackSimplexPathGeneratorsTargetMap f y n g := rfl

/-- The direct original-f morphism commutes with the actual literal-pullback second projection. -/
theorem nativeCoverPullbackSimplexPathGeneratorTargetMap_cover_square
    {X Y : SSet.{u}} (f : X ⟶ Y) (y : Y _⦋0⦌) :
    nativeCoverPullbackSimplexPathGeneratorTargetMap f y ≫
        (nativeCoverSimplexPathGeneratorIso Y y).hom =
      (nativeCoverPullbackSimplexPathGeneratorIso f y).hom ≫
        pullback.snd f (nativeCoverProjection Y y) := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.ext_apply
  intro g
  change nativeCoverSimplexPathGeneratorsEquiv Y y d.unop.len
      (nativeCoverPullbackSimplexPathGeneratorsTargetMap f y d.unop.len g) =
    (pullback.snd f (nativeCoverProjection Y y)).app d
      (nativeCoverPullbackSimplexPathGeneratorsEquiv f y d.unop.len g)
  exact nativeCoverPullbackSimplexPathGeneratorsTargetMap_equiv f y d.unop.len g

section Coefficients

variable {C : Type w} [Category.{v} C] [HasCoproducts.{u} C] [Preadditive C]

/-- The original target simplicial morphism induces its actual coefficient chain morphism. -/
noncomputable def nativeCoverPullbackRegularCoefficientChainTargetMap
    {X Y : SSet.{u}} (f : X ⟶ Y) (y : Y _⦋0⦌) (R : C) :
    (nativeCoverPullbackSimplexPathGeneratorSSet f y).chainComplex R ⟶
      nativeRegularCoefficientChainComplex Y y R :=
  SSet.chainComplexMap (nativeCoverPullbackSimplexPathGeneratorTargetMap f y) R

/-- The induced chain morphism sends each actual pair generator through the original-f map. -/
theorem nativeCoverPullbackRegularCoefficientChainTargetMap_on_generator
    {X Y : SSet.{u}} (f : X ⟶ Y) (y : Y _⦋0⦌) (R : C) {n : ℕ}
    (g : nativeCoverPullbackSimplexPathGenerators f y n) :
    (nativeCoverPullbackSimplexPathGeneratorSSet f y).ιChainComplex (R := R) g ≫
        (nativeCoverPullbackRegularCoefficientChainTargetMap f y R).f n =
      nativeRegularCoefficientChainGenerator Y y R
        (nativeCoverPullbackSimplexPathGeneratorsTargetMap f y n g) := by
  change (nativeCoverPullbackSimplexPathGeneratorSSet f y).ιChainComplex (R := R) g ≫
      (SSet.chainComplexMap (nativeCoverPullbackSimplexPathGeneratorTargetMap f y) R).f n = _
  exact (SSet.ι_chainComplexMap_f
      (X := nativeCoverPullbackSimplexPathGeneratorSSet f y)
      (Y := nativeCoverSimplexPathGeneratorSSet Y y)
      (f := nativeCoverPullbackSimplexPathGeneratorTargetMap f y) (R := R) (n := n)
      (show (nativeCoverPullbackSimplexPathGeneratorSSet f y) _⦋n⦌ from g)).trans
    (congrArg (fun h : (nativeCoverSimplexPathGeneratorSSet Y y) _⦋n⦌ =>
      (nativeCoverSimplexPathGeneratorSSet Y y).ιChainComplex (R := R) (n := n) h)
      (nativeCoverPullbackSimplexPathGeneratorTargetMap_app f y n g))

/-- The constructed chain morphism commutes with the actual cover comparisons and snd map. -/
theorem nativeCoverPullbackRegularCoefficientChainTargetMap_cover_square
    {X Y : SSet.{u}} (f : X ⟶ Y) (y : Y _⦋0⦌) (R : C) :
    nativeCoverPullbackRegularCoefficientChainTargetMap f y R ≫
        (nativeRegularCoefficientChainCoverIso Y y R).hom =
      (((SSet.chainComplexFunctor C).obj R).mapIso
          (nativeCoverPullbackSimplexPathGeneratorIso f y)).hom ≫
        SSet.chainComplexMap (pullback.snd f (nativeCoverProjection Y y)) R := by
  let F : SSet.{u} ⥤ ChainComplex C ℕ := (SSet.chainComplexFunctor C).obj R
  change F.map (nativeCoverPullbackSimplexPathGeneratorTargetMap f y) ≫
      F.map (nativeCoverSimplexPathGeneratorIso Y y).hom =
    F.map (nativeCoverPullbackSimplexPathGeneratorIso f y).hom ≫
      F.map (pullback.snd f (nativeCoverProjection Y y))
  exact (F.map_comp (nativeCoverPullbackSimplexPathGeneratorTargetMap f y)
      (nativeCoverSimplexPathGeneratorIso Y y).hom).symm.trans
    ((congrArg (fun h : nativeCoverPullbackSimplexPathGeneratorSSet f y ⟶ nativeCover Y y =>
        F.map h) (nativeCoverPullbackSimplexPathGeneratorTargetMap_cover_square f y)).trans
      (F.map_comp (nativeCoverPullbackSimplexPathGeneratorIso f y).hom
        (pullback.snd f (nativeCoverProjection Y y))))

end Coefficients

end SSet.KanComplex

namespace SSet.KanComplex

/-- The existing generator complex has the signed sum of actual direct module restrictions. -/
theorem nativeCoverPullbackGeneratorChainComplex_d
    {X Y : SSet.{u}} (f : X ⟶ Y) (y : Y _⦋0⦌) (n : ℕ) :
    ((nativeCoverPullbackSimplexPathGeneratorSSet f y).chainComplex
        (ModuleCat.of ℤ (ULift.{u} ℤ))).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        nativeCoverPullbackPathModuleRestriction f y (SimplexCategory.δ i) := by
  let Z : ModuleCat.{u} ℤ := ModuleCat.of ℤ (ULift.{u} ℤ)
  let G : SSet.{u} := nativeCoverPullbackSimplexPathGeneratorSSet f y
  let K : ChainComplex (ModuleCat.{u} ℤ) ℕ := G.chainComplex Z
  change K.d (n + 1) n =
    ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
      nativeCoverPullbackPathModuleRestriction f y (SimplexCategory.δ i)
  refine Limits.Sigma.hom_ext _ _ ?_
  intro p
  have hl : Limits.Sigma.ι (fun _ : nativeCoverPullbackSimplexPathGenerators f y (n + 1) => Z)
        p ≫ K.d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        Limits.Sigma.ι (fun _ : nativeCoverPullbackSimplexPathGenerators f y n => Z)
          (nativeCoverPullbackSimplexPathGeneratorsRestriction f y (SimplexCategory.δ i) p) := by
    change G.ιChainComplex (R := Z) p ≫ K.d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • G.ιChainComplex (R := Z) (G.δ i p)
    exact G.ιChainComplex_d Z p
  have hr : Limits.Sigma.ι (fun _ : nativeCoverPullbackSimplexPathGenerators f y (n + 1) => Z)
        p ≫ (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
          nativeCoverPullbackPathModuleRestriction f y (SimplexCategory.δ i)) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        Limits.Sigma.ι (fun _ : nativeCoverPullbackSimplexPathGenerators f y n => Z)
          (nativeCoverPullbackSimplexPathGeneratorsRestriction f y (SimplexCategory.δ i) p) := by
    rw [Preadditive.comp_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Preadditive.comp_zsmul]
    exact congrArg (fun h : Z ⟶ (∐ fun _ : nativeCoverPullbackSimplexPathGenerators f y n => Z) =>
      (-1 : ℤ) ^ i.val • h) (nativeCoverPullbackPathModuleRestriction_ι f y (SimplexCategory.δ i) p)
  exact hl.trans hr.symm

/-- The actual original differential commutes with the constructed original pullback basis. -/
theorem regularLocalCoefficientPullbackIntegralBasisIso_d
    {X Y : SSet.{u}} (f : X ⟶ Y) (y : Y _⦋0⦌) (n : ℕ) :
    (SSet.localCoefficientChainComplex ((SSet.mapFundamentalGroupoid f) ⋙
        CategoryTheory.regularPathModuleCoefficientFunctor (SSet.FundamentalGroupoid.mk y))).d
        (n + 1) n ≫ (regularLocalCoefficientPullbackIntegralBasisIso f y n).hom =
      (regularLocalCoefficientPullbackIntegralBasisIso f y (n + 1)).hom ≫
        ((nativeCoverPullbackSimplexPathGeneratorSSet f y).chainComplex
          (ModuleCat.of ℤ (ULift.{u} ℤ))).d (n + 1) n := by
  let L : SSet.LocalSystem ℤ X := (SSet.mapFundamentalGroupoid f) ⋙
    CategoryTheory.regularPathModuleCoefficientFunctor (SSet.FundamentalGroupoid.mk y)
  let Z : ModuleCat.{u} ℤ := ModuleCat.of ℤ (ULift.{u} ℤ)
  let A : ModuleCat.{u} ℤ := SSet.localCoefficientObj L (n + 1)
  let B : ModuleCat.{u} ℤ := SSet.localCoefficientObj L n
  let G1 : ModuleCat.{u} ℤ := ∐ fun _ : nativeCoverPullbackSimplexPathGenerators f y (n + 1) => Z
  let G0 : ModuleCat.{u} ℤ := ∐ fun _ : nativeCoverPullbackSimplexPathGenerators f y n => Z
  let dSource : A ⟶ B := (SSet.localCoefficientChainComplex L).d (n + 1) n
  let dTarget : G1 ⟶ G0 :=
    ((nativeCoverPullbackSimplexPathGeneratorSSet f y).chainComplex Z).d (n + 1) n
  let e0 : B ⟶ G0 := (regularLocalCoefficientPullbackIntegralBasisIso f y n).hom
  let e1 : A ⟶ G1 := (regularLocalCoefficientPullbackIntegralBasisIso f y (n + 1)).hom
  let faces : Fin (n + 2) → (A ⟶ B) := fun i => SSet.localCoefficientFace L i
  let nativeFaces : Fin (n + 2) → (G1 ⟶ G0) := fun i =>
    nativeCoverPullbackPathModuleRestriction f y (SimplexCategory.δ i)
  let signs : Fin (n + 2) → ℤ := fun i => (-1 : ℤ) ^ i.val
  have hSrc : dSource = ∑ i : Fin (n + 2), signs i • faces i :=
    SSet.localCoefficientChainComplex_d L n
  have hTarget : dTarget = ∑ i : Fin (n + 2), signs i • nativeFaces i :=
    nativeCoverPullbackGeneratorChainComplex_d f y n
  have hFace : ∀ i : Fin (n + 2), faces i ≫ e0 = e1 ≫ nativeFaces i := by
    intro i
    exact regularLocalCoefficientPullbackIntegralBasisIso_face f y i
  have hSourceComp : dSource ≫ e0 = (∑ i : Fin (n + 2), signs i • faces i) ≫ e0 :=
    congrArg (fun h : A ⟶ B => h ≫ e0) hSrc
  have hTargetComp : e1 ≫ dTarget = e1 ≫ (∑ i : Fin (n + 2), signs i • nativeFaces i) :=
    congrArg (fun h : G1 ⟶ G0 => e1 ≫ h) hTarget
  have hSumLeft : (∑ i : Fin (n + 2), signs i • faces i) ≫ e0 =
      ∑ i : Fin (n + 2), signs i • (faces i ≫ e0) :=
    (Preadditive.sum_comp (Finset.univ : Finset (Fin (n + 2)))
      (fun i => signs i • faces i) e0).trans
      (Finset.sum_congr rfl (fun i _ => Preadditive.zsmul_comp (faces i) e0 (signs i)))
  have hSumRight : e1 ≫ (∑ i : Fin (n + 2), signs i • nativeFaces i) =
      ∑ i : Fin (n + 2), signs i • (e1 ≫ nativeFaces i) :=
    (Preadditive.comp_sum (Finset.univ : Finset (Fin (n + 2))) e1
      (fun i => signs i • nativeFaces i)).trans
      (Finset.sum_congr rfl (fun i _ => Preadditive.comp_zsmul e1 (nativeFaces i) (signs i)))
  have hSumFaces : (∑ i : Fin (n + 2), signs i • (faces i ≫ e0)) =
      ∑ i : Fin (n + 2), signs i • (e1 ≫ nativeFaces i) :=
    Finset.sum_congr rfl (fun i _ =>
      congrArg (fun h : A ⟶ G0 => signs i • h) (hFace i))
  exact hSourceComp.trans
    (hSumLeft.trans (hSumFaces.trans (hSumRight.symm.trans hTargetComp.symm)))


/-- The actual original local-coefficient complex identifies with the independent generators. -/
noncomputable def regularLocalCoefficientPullbackGeneratorChainIso
    {X Y : SSet.{u}} (f : X ⟶ Y) (y : Y _⦋0⦌) :
    SSet.localCoefficientChainComplex ((SSet.mapFundamentalGroupoid f) ⋙
      CategoryTheory.regularPathModuleCoefficientFunctor (SSet.FundamentalGroupoid.mk y)) ≅
    (nativeCoverPullbackSimplexPathGeneratorSSet f y).chainComplex
      (ModuleCat.of ℤ (ULift.{u} ℤ)) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => regularLocalCoefficientPullbackIntegralBasisIso f y n) (by
      intro i j hij
      change j + 1 = i at hij
      subst i
      exact (regularLocalCoefficientPullbackIntegralBasisIso_d f y j).symm)

/-- Each forward degree component is the actual constructed original pullback basis map. -/
theorem regularLocalCoefficientPullbackGeneratorChainIso_hom_f
    {X Y : SSet.{u}} (f : X ⟶ Y) (y : Y _⦋0⦌) (n : ℕ) :
    (regularLocalCoefficientPullbackGeneratorChainIso f y).hom.f n =
      (regularLocalCoefficientPullbackIntegralBasisIso f y n).hom := rfl

/-- Each inverse degree component is the actual inverse of the original pullback basis. -/
theorem regularLocalCoefficientPullbackGeneratorChainIso_inv_f
    {X Y : SSet.{u}} (f : X ⟶ Y) (y : Y _⦋0⦌) (n : ℕ) :
    (regularLocalCoefficientPullbackGeneratorChainIso f y).inv.f n =
      (regularLocalCoefficientPullbackIntegralBasisIso f y n).inv := rfl

/-- The original complex compares with integral chains of the literal pulled-back cover. -/
noncomputable def regularLocalCoefficientPullbackCoverChainIso
    {X Y : SSet.{u}} (f : X ⟶ Y) (y : Y _⦋0⦌) :
    SSet.localCoefficientChainComplex ((SSet.mapFundamentalGroupoid f) ⋙
      CategoryTheory.regularPathModuleCoefficientFunctor (SSet.FundamentalGroupoid.mk y)) ≅
    (pullback f (nativeCoverProjection Y y)).chainComplex (ModuleCat.of ℤ (ULift.{u} ℤ)) :=
  regularLocalCoefficientPullbackGeneratorChainIso f y ≪≫
    (((SSet.chainComplexFunctor (ModuleCat.{u} ℤ)).obj (ModuleCat.of ℤ (ULift.{u} ℤ))).mapIso
      (nativeCoverPullbackSimplexPathGeneratorIso f y))

/-- The cover comparison preserves every integer on the actual lifted original generator. -/
theorem regularLocalCoefficientPullbackCoverChainIso_hom_ι_basis
    {X Y : SSet.{u}} (f : X ⟶ Y) (y : Y _⦋0⦌) (n : ℕ) (s : X _⦋n⦌)
    (γ : SSet.FundamentalGroupoid.mk y ⟶ (SSet.mapFundamentalGroupoid f).obj
      (ComposableArrows.left ((SSet.fundamentalGroupoidNerveUnit X).app (Opposite.op ⦋n⦌) s)))
    (z : ℤ) :
    (regularLocalCoefficientPullbackCoverChainIso f y).hom.f n
        (CategoryTheory.CategoryHomology.nervePullbackCoefficientι
          (SSet.fundamentalGroupoidNerveUnit X)
          ((SSet.mapFundamentalGroupoid f) ⋙ CategoryTheory.regularPathModuleCoefficientFunctor
            (SSet.FundamentalGroupoid.mk y)) s (z • FreeAbelianGroup.of γ)) =
      (pullback f (nativeCoverProjection Y y)).ιChainComplex
        (R := ModuleCat.of ℤ (ULift.{u} ℤ))
        (nativeCoverPullbackSimplexPathGeneratorsEquiv f y n
          (regularLocalCoefficientPullbackPathIndexEquiv f y n
            (regularLocalCoefficientPathIndexEquiv (SSet.mapFundamentalGroupoid f)
              (SSet.FundamentalGroupoid.mk y) n ⟨s, γ⟩))) (ULift.up z) := by
  let F : SSet.FundamentalGroupoid X ⥤ SSet.FundamentalGroupoid Y :=
    SSet.mapFundamentalGroupoid f
  let b : SSet.FundamentalGroupoid Y := SSet.FundamentalGroupoid.mk y
  let L : SSet.LocalSystem ℤ X := F ⋙ CategoryTheory.regularPathModuleCoefficientFunctor b
  let η := SSet.fundamentalGroupoidNerveUnit X
  let Z : ModuleCat.{u} ℤ := ModuleCat.of ℤ (ULift.{u} ℤ)
  let G : SSet.{u} := nativeCoverPullbackSimplexPathGeneratorSSet f y
  let W : SSet.{u} := pullback f (nativeCoverProjection Y y)
  let e : G ≅ W := nativeCoverPullbackSimplexPathGeneratorIso f y
  let p : nativeCoverPullbackSimplexPathGenerators f y n :=
    regularLocalCoefficientPullbackPathIndexEquiv f y n
      (regularLocalCoefficientPathIndexEquiv F b n ⟨s, γ⟩)
  let v : SSet.localCoefficientObj L n :=
    CategoryTheory.CategoryHomology.nervePullbackCoefficientι η L s (z • FreeAbelianGroup.of γ)
  have h0 : (regularLocalCoefficientPullbackIntegralBasisIso f y n).hom v =
      G.ιChainComplex (R := Z) p (ULift.up z) :=
    regularLocalCoefficientPullbackIntegralBasisIso_hom_ι_basis f y n s γ z
  have h1 : G.ιChainComplex (R := Z) p ≫ (SSet.chainComplexMap e.hom Z).f n =
      W.ιChainComplex (R := Z) (e.hom.app (Opposite.op ⦋n⦌) p) :=
    SSet.ι_chainComplexMap_f (X := G) (Y := W) (f := e.hom) (R := Z) (n := n)
      (show G _⦋n⦌ from p)
  have h2 : e.hom.app (Opposite.op ⦋n⦌) p =
      nativeCoverPullbackSimplexPathGeneratorsEquiv f y n p :=
    nativeCoverPullbackSimplexPathGeneratorIso_hom_app f y n p
  have h3 : G.ιChainComplex (R := Z) p ≫ (SSet.chainComplexMap e.hom Z).f n =
      W.ιChainComplex (R := Z) (nativeCoverPullbackSimplexPathGeneratorsEquiv f y n p) :=
    h1.trans (congrArg (fun w : W _⦋n⦌ => W.ιChainComplex (R := Z) w) h2)
  have hv := congrArg (fun h : Z ⟶ (W.chainComplex Z).X n => h (ULift.up z)) h3
  change (SSet.chainComplexMap e.hom Z).f n
      ((regularLocalCoefficientPullbackIntegralBasisIso f y n).hom v) =
    W.ιChainComplex (R := Z) (nativeCoverPullbackSimplexPathGeneratorsEquiv f y n p) (ULift.up z)
  exact (congrArg (fun w : (G.chainComplex Z).X n => (SSet.chainComplexMap e.hom Z).f n w)
    h0).trans hv

end SSet.KanComplex

namespace SSet.KanComplex

/-- The original target system has the generic basis at the actual identity groupoid functor. -/
noncomputable def originalNativeRegularCoefficientDegreeIso
    (Y : SSet.{u}) (y : Y _⦋0⦌) (n : ℕ) :
    SSet.localCoefficientObj
        (CategoryTheory.regularPathModuleCoefficientFunctor (SSet.FundamentalGroupoid.mk y)) n ≅
      (nativeRegularCoefficientChainComplex Y y (ModuleCat.of ℤ (ULift.{u} ℤ))).X n :=
  regularLocalCoefficientIntegralBasisIso (𝟭 (SSet.FundamentalGroupoid Y))
    (SSet.FundamentalGroupoid.mk y) n

/-- The original degree map sends every integral path generator to its actual native pair. -/
theorem originalNativeRegularCoefficientDegreeIso_hom_ι_basis
    (Y : SSet.{u}) (y : Y _⦋0⦌) (n : ℕ) (s : Y _⦋n⦌)
    (γ : SSet.FundamentalGroupoid.mk y ⟶ ComposableArrows.left
      ((SSet.fundamentalGroupoidNerveUnit Y).app (Opposite.op ⦋n⦌) s)) (z : ℤ) :
    (originalNativeRegularCoefficientDegreeIso Y y n).hom
        (CategoryTheory.CategoryHomology.nervePullbackCoefficientι
          (SSet.fundamentalGroupoidNerveUnit Y)
          (CategoryTheory.regularPathModuleCoefficientFunctor (SSet.FundamentalGroupoid.mk y))
          s (z • FreeAbelianGroup.of γ)) =
      nativeRegularCoefficientChainGenerator Y y (ModuleCat.of ℤ (ULift.{u} ℤ))
        (regularLocalCoefficientPathIndexEquiv (𝟭 (SSet.FundamentalGroupoid Y))
          (SSet.FundamentalGroupoid.mk y) n ⟨s, γ⟩) (ULift.up z) := by
  let I : SSet.FundamentalGroupoid Y ⥤ SSet.FundamentalGroupoid Y :=
    𝟭 (SSet.FundamentalGroupoid Y)
  let b : SSet.FundamentalGroupoid Y := SSet.FundamentalGroupoid.mk y
  let Z : ModuleCat.{u} ℤ := ModuleCat.of ℤ (ULift.{u} ℤ)
  let P : Type u := regularLocalCoefficientPathGenerators I b n
  have h := regularLocalCoefficientIntegralBasisIso_hom_ι_basis I b n s γ z
  have he := regularLocalCoefficientPathIndexEquiv_apply I b n s γ
  exact h.trans (congrArg (fun p : P => Limits.Sigma.ι (fun _ : P => Z) p (ULift.up z)) he.symm)

/-- The original target degree basis preserves each independently specified native face. -/
theorem originalNativeRegularCoefficientDegreeIso_face
    (Y : SSet.{u}) (y : Y _⦋0⦌) {n : ℕ} (i : Fin (n + 2)) :
    SSet.localCoefficientFace
        (CategoryTheory.regularPathModuleCoefficientFunctor (SSet.FundamentalGroupoid.mk y)) i ≫
        (originalNativeRegularCoefficientDegreeIso Y y n).hom =
      (originalNativeRegularCoefficientDegreeIso Y y (n + 1)).hom ≫
        regularLocalCoefficientPathModuleRestriction (𝟭 (SSet.FundamentalGroupoid Y))
          (SSet.FundamentalGroupoid.mk y) (SimplexCategory.δ i) :=
  regularLocalCoefficientIntegralBasisIso_face (𝟭 (SSet.FundamentalGroupoid Y))
    (SSet.FundamentalGroupoid.mk y) i

/-- The original target degree basis preserves every independently specified native degeneracy. -/
theorem originalNativeRegularCoefficientDegreeIso_degeneracy
    (Y : SSet.{u}) (y : Y _⦋0⦌) {n : ℕ} (i : Fin (n + 1)) :
    SSet.localCoefficientDegeneracy
        (CategoryTheory.regularPathModuleCoefficientFunctor (SSet.FundamentalGroupoid.mk y)) i ≫
        (originalNativeRegularCoefficientDegreeIso Y y (n + 1)).hom =
      (originalNativeRegularCoefficientDegreeIso Y y n).hom ≫
        regularLocalCoefficientPathModuleRestriction (𝟭 (SSet.FundamentalGroupoid Y))
          (SSet.FundamentalGroupoid.mk y) (SimplexCategory.σ i) :=
  regularLocalCoefficientIntegralBasisIso_degeneracy (𝟭 (SSet.FundamentalGroupoid Y))
    (SSet.FundamentalGroupoid.mk y) i

/-- The actual native target differential is the signed sum of direct identity path restrictions. -/
theorem nativeRegularCoefficientChainComplex_d_identityRestrictions
    (Y : SSet.{u}) (y : Y _⦋0⦌) (n : ℕ) :
    (nativeRegularCoefficientChainComplex Y y (ModuleCat.of ℤ (ULift.{u} ℤ))).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        regularLocalCoefficientPathModuleRestriction (𝟭 (SSet.FundamentalGroupoid Y))
          (SSet.FundamentalGroupoid.mk y) (SimplexCategory.δ i) := by
  let I : SSet.FundamentalGroupoid Y ⥤ SSet.FundamentalGroupoid Y :=
    𝟭 (SSet.FundamentalGroupoid Y)
  let b : SSet.FundamentalGroupoid Y := SSet.FundamentalGroupoid.mk y
  let Z : ModuleCat.{u} ℤ := ModuleCat.of ℤ (ULift.{u} ℤ)
  let K : ChainComplex (ModuleCat.{u} ℤ) ℕ := nativeRegularCoefficientChainComplex Y y Z
  change K.d (n + 1) n = ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
    regularLocalCoefficientPathModuleRestriction I b (SimplexCategory.δ i)
  refine Limits.Sigma.hom_ext _ _ ?_
  intro p
  have hl : Limits.Sigma.ι (fun _ : regularLocalCoefficientPathGenerators I b (n + 1) => Z) p ≫
        K.d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        Limits.Sigma.ι (fun _ : regularLocalCoefficientPathGenerators I b n => Z)
          (regularLocalCoefficientPathRestriction I b (SimplexCategory.δ i) p) := by
    change nativeRegularCoefficientChainGenerator Y y Z p ≫ K.d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • nativeRegularCoefficientChainGenerator Y y Z
        (nativeCoverSimplexPathGeneratorsRestriction Y y (SimplexCategory.δ i) p)
    exact nativeRegularCoefficientChainComplex_d_on_generator Y y Z p
  have hr : Limits.Sigma.ι (fun _ : regularLocalCoefficientPathGenerators I b (n + 1) => Z) p ≫
        (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
          regularLocalCoefficientPathModuleRestriction I b (SimplexCategory.δ i)) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        Limits.Sigma.ι (fun _ : regularLocalCoefficientPathGenerators I b n => Z)
          (regularLocalCoefficientPathRestriction I b (SimplexCategory.δ i) p) := by
    rw [Preadditive.comp_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Preadditive.comp_zsmul]
    exact congrArg (fun h : Z ⟶ (∐ fun _ : regularLocalCoefficientPathGenerators I b n => Z) =>
      (-1 : ℤ) ^ i.val • h)
      (regularLocalCoefficientPathModuleRestriction_ι I b (SimplexCategory.δ i) p)
  exact hl.trans hr.symm

/-- The original target differential commutes with the existing native degree basis. -/
theorem originalNativeRegularCoefficientDegreeIso_d
    (Y : SSet.{u}) (y : Y _⦋0⦌) (n : ℕ) :
    (SSet.localCoefficientChainComplex
        (CategoryTheory.regularPathModuleCoefficientFunctor (SSet.FundamentalGroupoid.mk y))).d
        (n + 1) n ≫ (originalNativeRegularCoefficientDegreeIso Y y n).hom =
      (originalNativeRegularCoefficientDegreeIso Y y (n + 1)).hom ≫
        (nativeRegularCoefficientChainComplex Y y (ModuleCat.of ℤ (ULift.{u} ℤ))).d (n + 1) n := by
  let I : SSet.FundamentalGroupoid Y ⥤ SSet.FundamentalGroupoid Y :=
    𝟭 (SSet.FundamentalGroupoid Y)
  let b : SSet.FundamentalGroupoid Y := SSet.FundamentalGroupoid.mk y
  let L : SSet.LocalSystem ℤ Y := CategoryTheory.regularPathModuleCoefficientFunctor b
  let Z : ModuleCat.{u} ℤ := ModuleCat.of ℤ (ULift.{u} ℤ)
  let A : ModuleCat.{u} ℤ := SSet.localCoefficientObj L (n + 1)
  let B : ModuleCat.{u} ℤ := SSet.localCoefficientObj L n
  let G1 : ModuleCat.{u} ℤ := ∐ fun _ : nativeCoverSimplexPathGenerators Y y (n + 1) => Z
  let G0 : ModuleCat.{u} ℤ := ∐ fun _ : nativeCoverSimplexPathGenerators Y y n => Z
  let dSource : A ⟶ B := (SSet.localCoefficientChainComplex L).d (n + 1) n
  let dTarget : G1 ⟶ G0 := (nativeRegularCoefficientChainComplex Y y Z).d (n + 1) n
  let e0 : B ⟶ G0 := (originalNativeRegularCoefficientDegreeIso Y y n).hom
  let e1 : A ⟶ G1 := (originalNativeRegularCoefficientDegreeIso Y y (n + 1)).hom
  let faces : Fin (n + 2) → (A ⟶ B) := fun i => SSet.localCoefficientFace L i
  let nativeFaces : Fin (n + 2) → (G1 ⟶ G0) := fun i =>
    regularLocalCoefficientPathModuleRestriction I b (SimplexCategory.δ i)
  let signs : Fin (n + 2) → ℤ := fun i => (-1 : ℤ) ^ i.val
  have hSrc : dSource = ∑ i : Fin (n + 2), signs i • faces i :=
    SSet.localCoefficientChainComplex_d L n
  have hTarget : dTarget = ∑ i : Fin (n + 2), signs i • nativeFaces i :=
    nativeRegularCoefficientChainComplex_d_identityRestrictions Y y n
  have hFace : ∀ i : Fin (n + 2), faces i ≫ e0 = e1 ≫ nativeFaces i := by
    intro i
    exact originalNativeRegularCoefficientDegreeIso_face Y y i
  have hSourceComp : dSource ≫ e0 = (∑ i : Fin (n + 2), signs i • faces i) ≫ e0 :=
    congrArg (fun h : A ⟶ B => h ≫ e0) hSrc
  have hTargetComp : e1 ≫ dTarget = e1 ≫ (∑ i : Fin (n + 2), signs i • nativeFaces i) :=
    congrArg (fun h : G1 ⟶ G0 => e1 ≫ h) hTarget
  have hSumLeft : (∑ i : Fin (n + 2), signs i • faces i) ≫ e0 =
      ∑ i : Fin (n + 2), signs i • (faces i ≫ e0) :=
    (Preadditive.sum_comp (Finset.univ : Finset (Fin (n + 2)))
      (fun i => signs i • faces i) e0).trans
      (Finset.sum_congr rfl (fun i _ => Preadditive.zsmul_comp (faces i) e0 (signs i)))
  have hSumRight : e1 ≫ (∑ i : Fin (n + 2), signs i • nativeFaces i) =
      ∑ i : Fin (n + 2), signs i • (e1 ≫ nativeFaces i) :=
    (Preadditive.comp_sum (Finset.univ : Finset (Fin (n + 2))) e1
      (fun i => signs i • nativeFaces i)).trans
      (Finset.sum_congr rfl (fun i _ => Preadditive.comp_zsmul e1 (nativeFaces i) (signs i)))
  have hSumFaces : (∑ i : Fin (n + 2), signs i • (faces i ≫ e0)) =
      ∑ i : Fin (n + 2), signs i • (e1 ≫ nativeFaces i) :=
    Finset.sum_congr rfl (fun i _ =>
      congrArg (fun h : A ⟶ G0 => signs i • h) (hFace i))
  exact hSourceComp.trans
    (hSumLeft.trans (hSumFaces.trans (hSumRight.symm.trans hTargetComp.symm)))


/-- The literal original target coefficient complex compares with the independent G19 complex. -/
noncomputable def originalNativeRegularCoefficientGeneratorChainIso
    (Y : SSet.{u}) (y : Y _⦋0⦌) :
    SSet.localCoefficientChainComplex
      (CategoryTheory.regularPathModuleCoefficientFunctor (SSet.FundamentalGroupoid.mk y)) ≅
    nativeRegularCoefficientChainComplex Y y (ModuleCat.of ℤ (ULift.{u} ℤ)) :=
  HomologicalComplex.Hom.isoOfComponents (fun n => originalNativeRegularCoefficientDegreeIso Y y n)
    (by
      intro i j hij
      change j + 1 = i at hij
      subst i
      exact (originalNativeRegularCoefficientDegreeIso_d Y y j).symm)

/-- The original target chain map has the actual generic identity-functor basis in every degree. -/
theorem originalNativeRegularCoefficientGeneratorChainIso_hom_f
    (Y : SSet.{u}) (y : Y _⦋0⦌) (n : ℕ) :
    (originalNativeRegularCoefficientGeneratorChainIso Y y).hom.f n =
      (originalNativeRegularCoefficientDegreeIso Y y n).hom := rfl

/-- Its inverse component is the actual inverse of that existing generic degree basis. -/
theorem originalNativeRegularCoefficientGeneratorChainIso_inv_f
    (Y : SSet.{u}) (y : Y _⦋0⦌) (n : ℕ) :
    (originalNativeRegularCoefficientGeneratorChainIso Y y).inv.f n =
      (originalNativeRegularCoefficientDegreeIso Y y n).inv := rfl

/-- The original target regular complex compares with integral chains of its actual native cover. -/
noncomputable def originalNativeRegularCoefficientCoverChainIso
    (Y : SSet.{u}) (y : Y _⦋0⦌) :
    SSet.localCoefficientChainComplex
      (CategoryTheory.regularPathModuleCoefficientFunctor (SSet.FundamentalGroupoid.mk y)) ≅
    (nativeCover Y y).chainComplex (ModuleCat.of ℤ (ULift.{u} ℤ)) :=
  originalNativeRegularCoefficientGeneratorChainIso Y y ≪≫
    nativeRegularCoefficientChainCoverIso Y y (ModuleCat.of ℤ (ULift.{u} ℤ))

/-- The original target comparison preserves every integer on its actual lifted generator. -/
theorem originalNativeRegularCoefficientCoverChainIso_hom_ι_basis
    (Y : SSet.{u}) (y : Y _⦋0⦌) (n : ℕ) (s : Y _⦋n⦌)
    (γ : SSet.FundamentalGroupoid.mk y ⟶ ComposableArrows.left
      ((SSet.fundamentalGroupoidNerveUnit Y).app (Opposite.op ⦋n⦌) s)) (z : ℤ) :
    (originalNativeRegularCoefficientCoverChainIso Y y).hom.f n
        (CategoryTheory.CategoryHomology.nervePullbackCoefficientι
          (SSet.fundamentalGroupoidNerveUnit Y)
          (CategoryTheory.regularPathModuleCoefficientFunctor (SSet.FundamentalGroupoid.mk y))
          s (z • FreeAbelianGroup.of γ)) =
      (nativeCover Y y).ιChainComplex (R := ModuleCat.of ℤ (ULift.{u} ℤ))
        (nativeCoverSimplexPathGeneratorsEquiv Y y n
          (regularLocalCoefficientPathIndexEquiv (𝟭 (SSet.FundamentalGroupoid Y))
            (SSet.FundamentalGroupoid.mk y) n ⟨s, γ⟩)) (ULift.up z) := by
  let I : SSet.FundamentalGroupoid Y ⥤ SSet.FundamentalGroupoid Y :=
    𝟭 (SSet.FundamentalGroupoid Y)
  let b : SSet.FundamentalGroupoid Y := SSet.FundamentalGroupoid.mk y
  let L : SSet.LocalSystem ℤ Y := CategoryTheory.regularPathModuleCoefficientFunctor b
  let η := SSet.fundamentalGroupoidNerveUnit Y
  let Z : ModuleCat.{u} ℤ := ModuleCat.of ℤ (ULift.{u} ℤ)
  let p : nativeCoverSimplexPathGenerators Y y n :=
    regularLocalCoefficientPathIndexEquiv I b n ⟨s, γ⟩
  let v : SSet.localCoefficientObj L n :=
    CategoryTheory.CategoryHomology.nervePullbackCoefficientι η L s (z • FreeAbelianGroup.of γ)
  have h0 : (originalNativeRegularCoefficientDegreeIso Y y n).hom v =
      nativeRegularCoefficientChainGenerator Y y Z p (ULift.up z) :=
    originalNativeRegularCoefficientDegreeIso_hom_ι_basis Y y n s γ z
  have h1 : nativeRegularCoefficientChainGenerator Y y Z p ≫
        (nativeRegularCoefficientChainCoverIso Y y Z).hom.f n =
      (nativeCover Y y).ιChainComplex (R := Z) (nativeCoverSimplexPathGeneratorsEquiv Y y n p) :=
    nativeRegularCoefficientChainCoverIso_on_generator Y y Z p
  have hv := congrArg (fun h : Z ⟶ ((nativeCover Y y).chainComplex Z).X n => h (ULift.up z)) h1
  change (nativeRegularCoefficientChainCoverIso Y y Z).hom.f n
      ((originalNativeRegularCoefficientDegreeIso Y y n).hom v) =
    (nativeCover Y y).ιChainComplex (R := Z)
      (nativeCoverSimplexPathGeneratorsEquiv Y y n p) (ULift.up z)
  exact (congrArg (fun w : (nativeRegularCoefficientChainComplex Y y Z).X n =>
    (nativeRegularCoefficientChainCoverIso Y y Z).hom.f n w) h0).trans hv

end SSet.KanComplex


namespace SSet.KanComplex

/-- The actual original pullback chain map preserves every integer path generator,
transporting its endpoint by the computed nerve-unit equality before the target inclusion. -/
theorem originalRegularPullbackChainMap_generator
    {X Y : SSet.{u}} (f : X ⟶ Y) (y : Y _⦋0⦌) (n : ℕ)
    (s : X _⦋n⦌)
    (γ : SSet.FundamentalGroupoid.mk y ⟶ (SSet.mapFundamentalGroupoid f).obj
      (ComposableArrows.left
        ((SSet.fundamentalGroupoidNerveUnit X).app (Opposite.op ⦋n⦌) s)))
    (z : ℤ) :
    let L : SSet.LocalSystem ℤ Y :=
      CategoryTheory.regularPathModuleCoefficientFunctor (SSet.FundamentalGroupoid.mk y)
    (SSet.localCoefficientPullbackChainMap f L).f n
        (CategoryTheory.CategoryHomology.nervePullbackCoefficientι
          (SSet.fundamentalGroupoidNerveUnit X) (L.pullback f) s
          (z • FreeAbelianGroup.of γ)) =
      CategoryTheory.CategoryHomology.nervePullbackCoefficientι
        (SSet.fundamentalGroupoidNerveUnit Y) L (f.app (Opposite.op ⦋n⦌) s)
        (z • FreeAbelianGroup.of
          (γ ≫ eqToHom (SSet.localCoefficientPullbackLeftIndex f s).symm)) := by
  let b := SSet.FundamentalGroupoid.mk y
  let L : SSet.LocalSystem ℤ Y := CategoryTheory.regularPathModuleCoefficientFunctor b
  let ηX := SSet.fundamentalGroupoidNerveUnit X
  let ηY := SSet.fundamentalGroupoidNerveUnit Y
  let t : Y _⦋n⦌ := f.app (Opposite.op ⦋n⦌) s
  let x : SSet.FundamentalGroupoid Y := (SSet.mapFundamentalGroupoid f).obj
    (ComposableArrows.left (ηX.app (Opposite.op ⦋n⦌) s))
  let x' : SSet.FundamentalGroupoid Y :=
    ComposableArrows.left (ηY.app (Opposite.op ⦋n⦌) t)
  let μ : x = x' := (SSet.localCoefficientPullbackLeftIndex f s).symm
  let A0 : ModuleCat.{u} ℤ := SSet.localCoefficientFamily (L.pullback f) n s
  let B0 : ModuleCat.{u} ℤ := SSet.localCoefficientFamily L n t
  let B : ModuleCat.{u} ℤ := SSet.localCoefficientObj L n
  let c : A0 ⟶ B0 := eqToHom (SSet.localCoefficientPullbackFamilyEq f L s)
  let M := SSet.localCoefficientPullbackChainMap f L
  have hc : c = L.map (eqToHom μ) := by
    change eqToHom (congrArg L.obj μ) = L.map (eqToHom μ)
    exact (eqToHom_map L μ).symm
  have hγ : L.map (eqToHom μ) (FreeAbelianGroup.of γ : A0) =
      (FreeAbelianGroup.of (γ ≫ eqToHom μ) : B0) :=
    CategoryTheory.regularPathModuleCoefficientFunctor_map_of b (eqToHom μ) γ
  have hg : c (FreeAbelianGroup.of γ : A0) =
      (FreeAbelianGroup.of (γ ≫ eqToHom μ) : B0) :=
    (congrArg (fun h : A0 ⟶ B0 => h (FreeAbelianGroup.of γ : A0)) hc).trans hγ
  have hz : c (z • (FreeAbelianGroup.of γ : A0)) =
      z • (FreeAbelianGroup.of (γ ≫ eqToHom μ) : B0) :=
    (c.hom.map_smul z (FreeAbelianGroup.of γ : A0)).trans
      (congrArg (fun a : B0 => z • a) hg)
  have hi : CategoryTheory.CategoryHomology.nervePullbackCoefficientι ηX (L.pullback f) s ≫
        M.f n = c ≫ CategoryTheory.CategoryHomology.nervePullbackCoefficientι ηY L t :=
    SSet.localCoefficientι_pullbackChainMap f L s
  have hv : M.f n
        (CategoryTheory.CategoryHomology.nervePullbackCoefficientι ηX (L.pullback f) s
          (z • (FreeAbelianGroup.of γ : A0))) =
      CategoryTheory.CategoryHomology.nervePullbackCoefficientι ηY L t
        (c (z • (FreeAbelianGroup.of γ : A0))) :=
    congrArg (fun h : A0 ⟶ B => h (z • (FreeAbelianGroup.of γ : A0))) hi
  change M.f n
      (CategoryTheory.CategoryHomology.nervePullbackCoefficientι ηX (L.pullback f) s
        (z • (FreeAbelianGroup.of γ : A0))) =
    CategoryTheory.CategoryHomology.nervePullbackCoefficientι ηY L t
      (z • (FreeAbelianGroup.of (γ ≫ eqToHom μ) : B0))
  exact hv.trans
    (congrArg (fun a : B0 => CategoryTheory.CategoryHomology.nervePullbackCoefficientι ηY L t a)
      hz)

end SSet.KanComplex


namespace SSet.KanComplex

/-- The original image-coefficient cast agrees with the computed source and target index casts. -/
theorem originalRegularPullbackPathIndexTransport
    {X Y : SSet.{u}} (f : X ⟶ Y) {n : ℕ} (s : X _⦋n⦌) :
    let σ : (Δ[n] : SSet.{u}) ⟶ X := SSet.yonedaEquiv.symm s
    let t : Y _⦋n⦌ := f.app (Opposite.op ⦋n⦌) s
    let τ : (Δ[n] : SSet.{u}) ⟶ Y := SSet.yonedaEquiv.symm t
    let α : (Δ[0] : SSet.{u}) ⟶ Δ[n] := SSet.yonedaEquiv.symm
      (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1)))
    let ρ : τ = σ ≫ f := (SSet.yonedaEquiv_symm_comp s f).symm
    let ν := congrArg (fun ζ : (Δ[n] : SSet.{u}) ⟶ Y =>
      SSet.FundamentalGroupoid.mk ((SSet.yonedaEquiv (n := ⦋0⦌)) (α ≫ ζ))) ρ
    (eqToHom (SSet.localCoefficientPullbackLeftIndex f s).symm ≫
        eqToHom (regularLocalCoefficientFirstObject_eq t)) ≫ eqToHom ν =
      (SSet.mapFundamentalGroupoid f).map (eqToHom (regularLocalCoefficientFirstObject_eq s)) ≫
        eqToHom (regularLocalCoefficientPullbackEndpoint_eq f σ) := by
  let F := SSet.mapFundamentalGroupoid f
  let σ : (Δ[n] : SSet.{u}) ⟶ X := SSet.yonedaEquiv.symm s
  let t : Y _⦋n⦌ := f.app (Opposite.op ⦋n⦌) s
  let τ : (Δ[n] : SSet.{u}) ⟶ Y := SSet.yonedaEquiv.symm t
  let α : (Δ[0] : SSet.{u}) ⟶ Δ[n] := SSet.yonedaEquiv.symm
    (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1)))
  let A : SSet.FundamentalGroupoid X := ComposableArrows.left
    ((SSet.fundamentalGroupoidNerveUnit X).app (Opposite.op ⦋n⦌) s)
  let B : SSet.FundamentalGroupoid Y := ComposableArrows.left
    ((SSet.fundamentalGroupoidNerveUnit Y).app (Opposite.op ⦋n⦌) t)
  let VX : SSet.FundamentalGroupoid X :=
    SSet.FundamentalGroupoid.mk ((SSet.yonedaEquiv (n := ⦋0⦌)) (α ≫ σ))
  let VY : SSet.FundamentalGroupoid Y :=
    SSet.FundamentalGroupoid.mk ((SSet.yonedaEquiv (n := ⦋0⦌)) (α ≫ τ))
  let V : SSet.FundamentalGroupoid Y :=
    SSet.FundamentalGroupoid.mk ((SSet.yonedaEquiv (n := ⦋0⦌)) (α ≫ (σ ≫ f)))
  let μ : F.obj A = B := (SSet.localCoefficientPullbackLeftIndex f s).symm
  let κX : A = VX := regularLocalCoefficientFirstObject_eq s
  let κY : B = VY := regularLocalCoefficientFirstObject_eq t
  let χ : F.obj VX = V := regularLocalCoefficientPullbackEndpoint_eq f σ
  let ρ : τ = σ ≫ f := (SSet.yonedaEquiv_symm_comp s f).symm
  let ν : VY = V := congrArg (fun ζ : (Δ[n] : SSet.{u}) ⟶ Y =>
    SSet.FundamentalGroupoid.mk ((SSet.yonedaEquiv (n := ⦋0⦌)) (α ≫ ζ))) ρ
  have hL : (eqToHom μ ≫ eqToHom κY) ≫ eqToHom ν =
      eqToHom ((μ.trans κY).trans ν) :=
    (congrArg (fun h : F.obj A ⟶ VY => h ≫ eqToHom ν) (eqToHom_trans μ κY)).trans
      (eqToHom_trans (μ.trans κY) ν)
  have hR : F.map (eqToHom κX) ≫ eqToHom χ =
      eqToHom ((congrArg F.obj κX).trans χ) :=
    (congrArg (fun h : F.obj A ⟶ F.obj VX => h ≫ eqToHom χ)
      (eqToHom_map F κX)).trans (eqToHom_trans (congrArg F.obj κX) χ)
  have hP : (μ.trans κY).trans ν = (congrArg F.obj κX).trans χ :=
    Subsingleton.elim _ _
  have h := congrArg (fun h : F.obj A = V => eqToHom h) hP
  change (eqToHom μ ≫ eqToHom κY) ≫ eqToHom ν = F.map (eqToHom κX) ≫ eqToHom χ
  exact hL.trans (h.trans hR.symm)

/-- The actual original-f coefficient path maps to the independent target generator index. -/
theorem originalRegularPullbackPathIndexEquiv_targetMap
    {X Y : SSet.{u}} (f : X ⟶ Y) (y : Y _⦋0⦌) (n : ℕ)
    (s : X _⦋n⦌)
    (γ : SSet.FundamentalGroupoid.mk y ⟶ (SSet.mapFundamentalGroupoid f).obj
      (ComposableArrows.left
        ((SSet.fundamentalGroupoidNerveUnit X).app (Opposite.op ⦋n⦌) s))) :
    (show nativeCoverSimplexPathGenerators Y y n from
      regularLocalCoefficientPathIndexEquiv (𝟭 (SSet.FundamentalGroupoid Y))
        (SSet.FundamentalGroupoid.mk y) n
        ⟨f.app (Opposite.op ⦋n⦌) s,
          γ ≫ eqToHom (SSet.localCoefficientPullbackLeftIndex f s).symm⟩) =
      nativeCoverPullbackSimplexPathGeneratorsTargetMap f y n
        (regularLocalCoefficientPullbackPathIndexEquiv f y n
          (regularLocalCoefficientPathIndexEquiv (SSet.mapFundamentalGroupoid f)
            (SSet.FundamentalGroupoid.mk y) n ⟨s, γ⟩)) := by
  let F := SSet.mapFundamentalGroupoid f
  let b := SSet.FundamentalGroupoid.mk y
  let σ : (Δ[n] : SSet.{u}) ⟶ X := SSet.yonedaEquiv.symm s
  let t : Y _⦋n⦌ := f.app (Opposite.op ⦋n⦌) s
  let τ : (Δ[n] : SSet.{u}) ⟶ Y := SSet.yonedaEquiv.symm t
  let α : (Δ[0] : SSet.{u}) ⟶ Δ[n] := SSet.yonedaEquiv.symm
    (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1)))
  let A : SSet.FundamentalGroupoid X := ComposableArrows.left
    ((SSet.fundamentalGroupoidNerveUnit X).app (Opposite.op ⦋n⦌) s)
  let B : SSet.FundamentalGroupoid Y := ComposableArrows.left
    ((SSet.fundamentalGroupoidNerveUnit Y).app (Opposite.op ⦋n⦌) t)
  let VX : SSet.FundamentalGroupoid X :=
    SSet.FundamentalGroupoid.mk ((SSet.yonedaEquiv (n := ⦋0⦌)) (α ≫ σ))
  let VY : SSet.FundamentalGroupoid Y :=
    SSet.FundamentalGroupoid.mk ((SSet.yonedaEquiv (n := ⦋0⦌)) (α ≫ τ))
  let V : SSet.FundamentalGroupoid Y :=
    SSet.FundamentalGroupoid.mk ((SSet.yonedaEquiv (n := ⦋0⦌)) (α ≫ (σ ≫ f)))
  let μ : F.obj A = B := (SSet.localCoefficientPullbackLeftIndex f s).symm
  let κX : A = VX := regularLocalCoefficientFirstObject_eq s
  let κY : B = VY := regularLocalCoefficientFirstObject_eq t
  let χ : F.obj VX = V := regularLocalCoefficientPullbackEndpoint_eq f σ
  let ρ : τ = σ ≫ f := (SSet.yonedaEquiv_symm_comp s f).symm
  let ν : VY = V := congrArg (fun ζ : (Δ[n] : SSet.{u}) ⟶ Y =>
    SSet.FundamentalGroupoid.mk ((SSet.yonedaEquiv (n := ⦋0⦌)) (α ≫ ζ))) ρ
  let γ1 : b ⟶ F.obj VX := γ ≫ eqToHom (congrArg F.obj κX)
  let u0 : b ⟶ VY := (γ ≫ eqToHom μ) ≫ eqToHom κY
  let v0 : b ⟶ V := γ1 ≫ eqToHom χ
  let EF := regularLocalCoefficientPathIndexEquiv F b n
  let EI := regularLocalCoefficientPathIndexEquiv (𝟭 (SSet.FundamentalGroupoid Y)) b n
  let Q := regularLocalCoefficientPullbackPathIndexEquiv f y n
  let Λ := nativeCoverPullbackSimplexPathGeneratorsTargetMap f y n
  have h0 : (eqToHom μ ≫ eqToHom κY) ≫ eqToHom ν =
      F.map (eqToHom κX) ≫ eqToHom χ := originalRegularPullbackPathIndexTransport f s
  have hm : F.map (eqToHom κX) ≫ eqToHom χ =
      eqToHom (congrArg F.obj κX) ≫ eqToHom χ :=
    congrArg (fun h : F.obj A ⟶ F.obj VX => h ≫ eqToHom χ) (eqToHom_map F κX)
  have hc := h0.trans hm
  have hpath : u0 ≫ eqToHom ν = v0 := by
    have h := congrArg (fun h : F.obj A ⟶ V => γ ≫ h) hc
    simpa only [u0, v0, γ1, Category.assoc] using h
  have hl : (show nativeCoverSimplexPathGenerators Y y n from
        EI ⟨t, γ ≫ eqToHom μ⟩) =
      (⟨τ, u0⟩ : nativeCoverSimplexPathGenerators Y y n) :=
    regularLocalCoefficientPathIndexEquiv_apply (𝟭 (SSet.FundamentalGroupoid Y)) b n t
      (γ ≫ eqToHom μ)
  have hEF : EF ⟨s, γ⟩ = (⟨σ, γ1⟩ : regularLocalCoefficientPathGenerators F b n) :=
    regularLocalCoefficientPathIndexEquiv_apply F b n s γ
  have hQ : Q (EF ⟨s, γ⟩) =
      (⟨σ, v0⟩ : nativeCoverPullbackSimplexPathGenerators f y n) :=
    (congrArg (fun p : regularLocalCoefficientPathGenerators F b n => Q p) hEF).trans
      (regularLocalCoefficientPullbackPathIndexEquiv_apply f y n
        (show regularLocalCoefficientPathGenerators F b n from ⟨σ, γ1⟩))
  have hr : Λ (Q (EF ⟨s, γ⟩)) =
      (⟨σ ≫ f, v0⟩ : nativeCoverSimplexPathGenerators Y y n) :=
    congrArg (fun p : nativeCoverPullbackSimplexPathGenerators f y n => Λ p) hQ
  have hbase : (⟨τ, u0⟩ : nativeCoverSimplexPathGenerators Y y n) =
      (⟨σ ≫ f, u0 ≫ eqToHom ν⟩ : nativeCoverSimplexPathGenerators Y y n) :=
    (nativeGenerator_baseCast y
      (show nativeCoverSimplexPathGenerators Y y n from ⟨τ, u0⟩) (σ ≫ f) ρ).symm
  have hpair : (⟨τ, u0⟩ : nativeCoverSimplexPathGenerators Y y n) =
      (⟨σ ≫ f, v0⟩ : nativeCoverSimplexPathGenerators Y y n) :=
    hbase.trans (congrArg (fun δ : b ⟶ V =>
      (⟨σ ≫ f, δ⟩ : nativeCoverSimplexPathGenerators Y y n)) hpath)
  change (show nativeCoverSimplexPathGenerators Y y n from EI ⟨t, γ ≫ eqToHom μ⟩) =
    Λ (Q (EF ⟨s, γ⟩))
  exact hl.trans (hpair.trans hr.symm)

end SSet.KanComplex

namespace SSet.KanComplex

/-- The actual original pullback chain map commutes with the two independent generator bases. -/
theorem originalRegularPullbackChainMap_generator_square
    {X Y : SSet.{u}} (f : X ⟶ Y) (y : Y _⦋0⦌) :
    let L : SSet.LocalSystem ℤ Y :=
      CategoryTheory.regularPathModuleCoefficientFunctor (SSet.FundamentalGroupoid.mk y)
    SSet.localCoefficientPullbackChainMap f L ≫
        (originalNativeRegularCoefficientGeneratorChainIso Y y).hom =
      (regularLocalCoefficientPullbackGeneratorChainIso f y).hom ≫
        nativeCoverPullbackRegularCoefficientChainTargetMap f y (ModuleCat.of ℤ (ULift.{u} ℤ)) := by
  let L : SSet.LocalSystem ℤ Y := CategoryTheory.regularPathModuleCoefficientFunctor
    (SSet.FundamentalGroupoid.mk y)
  let Z : ModuleCat.{u} ℤ := ModuleCat.of ℤ (ULift.{u} ℤ)
  let A : ChainComplex (ModuleCat.{u} ℤ) ℕ := SSet.localCoefficientChainComplex (L.pullback f)
  let B : ChainComplex (ModuleCat.{u} ℤ) ℕ := SSet.localCoefficientChainComplex L
  let G : SSet.{u} := nativeCoverPullbackSimplexPathGeneratorSSet f y
  let S : ChainComplex (ModuleCat.{u} ℤ) ℕ := G.chainComplex Z
  let T : ChainComplex (ModuleCat.{u} ℤ) ℕ := nativeRegularCoefficientChainComplex Y y Z
  let M : A ⟶ B := SSet.localCoefficientPullbackChainMap f L
  let eS : A ≅ S := regularLocalCoefficientPullbackGeneratorChainIso f y
  let eT : B ≅ T := originalNativeRegularCoefficientGeneratorChainIso Y y
  let D : S ⟶ T := nativeCoverPullbackRegularCoefficientChainTargetMap f y Z
  change M ≫ eT.hom = eS.hom ≫ D
  refine HomologicalComplex.hom_ext _ _ ?_
  intro n
  change M.f n ≫ eT.hom.f n = eS.hom.f n ≫ D.f n
  refine Limits.Sigma.hom_ext _ _ ?_
  intro s
  apply ModuleCat.hom_ext
  apply LinearMap.toAddMonoidHom_injective
  refine FreeAbelianGroup.lift_ext _ _ ?_
  intro γ
  let ηX := SSet.fundamentalGroupoidNerveUnit X
  let ηY := SSet.fundamentalGroupoidNerveUnit Y
  let t : Y _⦋n⦌ := f.app (Opposite.op ⦋n⦌) s
  let μ : (SSet.mapFundamentalGroupoid f).obj
      (ComposableArrows.left (ηX.app (Opposite.op ⦋n⦌) s)) =
    ComposableArrows.left (ηY.app (Opposite.op ⦋n⦌) t) :=
      (SSet.localCoefficientPullbackLeftIndex f s).symm
  let δ : SSet.FundamentalGroupoid.mk y ⟶
      ComposableArrows.left (ηY.app (Opposite.op ⦋n⦌) t) := γ ≫ eqToHom μ
  let A0 : ModuleCat.{u} ℤ := SSet.localCoefficientFamily (L.pullback f) n s
  let B0 : ModuleCat.{u} ℤ := SSet.localCoefficientFamily L n t
  let iS : A0 ⟶ A.X n :=
    CategoryTheory.CategoryHomology.nervePullbackCoefficientι ηX (L.pullback f) s
  let iT : B0 ⟶ B.X n :=
    CategoryTheory.CategoryHomology.nervePullbackCoefficientι ηY L t
  let pS : nativeCoverPullbackSimplexPathGenerators f y n :=
    regularLocalCoefficientPullbackPathIndexEquiv f y n
      (regularLocalCoefficientPathIndexEquiv (SSet.mapFundamentalGroupoid f)
        (SSet.FundamentalGroupoid.mk y) n ⟨s, γ⟩)
  let pT : nativeCoverSimplexPathGenerators Y y n :=
    regularLocalCoefficientPathIndexEquiv (𝟭 (SSet.FundamentalGroupoid Y))
      (SSet.FundamentalGroupoid.mk y) n ⟨t, δ⟩
  let Λ := nativeCoverPullbackSimplexPathGeneratorsTargetMap f y n
  have hm1 : (iS ≫ M.f n) ((1 : ℤ) • (FreeAbelianGroup.of γ : A0)) =
      iT ((1 : ℤ) • (FreeAbelianGroup.of δ : B0)) :=
    originalRegularPullbackChainMap_generator f y n s γ (1 : ℤ)
  have hm : (iS ≫ M.f n) (FreeAbelianGroup.of γ : A0) =
      iT (FreeAbelianGroup.of δ : B0) :=
    (congrArg (fun a : A0 => (iS ≫ M.f n) a)
      (one_smul ℤ (FreeAbelianGroup.of γ : A0)).symm).trans
        (hm1.trans (congrArg (fun a : B0 => iT a)
          (one_smul ℤ (FreeAbelianGroup.of δ : B0))))
  have hTF : eT.hom.f n = (originalNativeRegularCoefficientDegreeIso Y y n).hom :=
    originalNativeRegularCoefficientGeneratorChainIso_hom_f Y y n
  have ht1 : (iT ≫ eT.hom.f n) ((1 : ℤ) • (FreeAbelianGroup.of δ : B0)) =
      nativeRegularCoefficientChainGenerator Y y Z pT (ULift.up (1 : ℤ)) :=
    (congrArg (fun h : B.X n ⟶ T.X n =>
      h (iT ((1 : ℤ) • (FreeAbelianGroup.of δ : B0)))) hTF).trans
        (originalNativeRegularCoefficientDegreeIso_hom_ι_basis Y y n t δ (1 : ℤ))
  have ht : (iT ≫ eT.hom.f n) (FreeAbelianGroup.of δ : B0) =
      nativeRegularCoefficientChainGenerator Y y Z pT (ULift.up (1 : ℤ)) :=
    (congrArg (fun a : B0 => (iT ≫ eT.hom.f n) a)
      (one_smul ℤ (FreeAbelianGroup.of δ : B0)).symm).trans ht1
  have hSF : eS.hom.f n = (regularLocalCoefficientPullbackIntegralBasisIso f y n).hom :=
    regularLocalCoefficientPullbackGeneratorChainIso_hom_f f y n
  have hs1 : (iS ≫ eS.hom.f n) ((1 : ℤ) • (FreeAbelianGroup.of γ : A0)) =
      G.ιChainComplex (R := Z) pS (ULift.up (1 : ℤ)) :=
    (congrArg (fun h : A.X n ⟶ S.X n =>
      h (iS ((1 : ℤ) • (FreeAbelianGroup.of γ : A0)))) hSF).trans
        (regularLocalCoefficientPullbackIntegralBasisIso_hom_ι_basis f y n s γ (1 : ℤ))
  have hs : (iS ≫ eS.hom.f n) (FreeAbelianGroup.of γ : A0) =
      G.ιChainComplex (R := Z) pS (ULift.up (1 : ℤ)) :=
    (congrArg (fun a : A0 => (iS ≫ eS.hom.f n) a)
      (one_smul ℤ (FreeAbelianGroup.of γ : A0)).symm).trans hs1
  have hdM : G.ιChainComplex (R := Z) pS ≫ D.f n =
      nativeRegularCoefficientChainGenerator Y y Z (Λ pS) :=
    nativeCoverPullbackRegularCoefficientChainTargetMap_on_generator f y Z pS
  have hd : D.f n (G.ιChainComplex (R := Z) pS (ULift.up (1 : ℤ))) =
      nativeRegularCoefficientChainGenerator Y y Z (Λ pS) (ULift.up (1 : ℤ)) :=
    congrArg (fun h : Z ⟶ T.X n => h (ULift.up (1 : ℤ))) hdM
  have hp : pT = Λ pS := originalRegularPullbackPathIndexEquiv_targetMap f y n s γ
  have hgen := congrArg (fun p : nativeCoverSimplexPathGenerators Y y n =>
    nativeRegularCoefficientChainGenerator Y y Z p (ULift.up (1 : ℤ))) hp
  have hl : eT.hom.f n (M.f n (iS (FreeAbelianGroup.of γ : A0))) =
      nativeRegularCoefficientChainGenerator Y y Z pT (ULift.up (1 : ℤ)) :=
    (congrArg (fun a : B.X n => eT.hom.f n a) hm).trans ht
  have hr : D.f n (eS.hom.f n (iS (FreeAbelianGroup.of γ : A0))) =
      nativeRegularCoefficientChainGenerator Y y Z (Λ pS) (ULift.up (1 : ℤ)) :=
    (congrArg (fun a : S.X n => D.f n a) hs).trans hd
  change eT.hom.f n (M.f n (iS (FreeAbelianGroup.of γ : A0))) =
    D.f n (eS.hom.f n (iS (FreeAbelianGroup.of γ : A0)))
  exact hl.trans (hgen.trans hr.symm)

/-- The actual original coefficient map commutes with chains of the literal pulled-back cover. -/
theorem originalRegularPullbackChainMap_cover_square
    {X Y : SSet.{u}} (f : X ⟶ Y) (y : Y _⦋0⦌) :
    let L : SSet.LocalSystem ℤ Y :=
      CategoryTheory.regularPathModuleCoefficientFunctor (SSet.FundamentalGroupoid.mk y)
    SSet.localCoefficientPullbackChainMap f L ≫
        (originalNativeRegularCoefficientCoverChainIso Y y).hom =
      (regularLocalCoefficientPullbackCoverChainIso f y).hom ≫
        SSet.chainComplexMap (pullback.snd f (nativeCoverProjection Y y))
          (ModuleCat.of ℤ (ULift.{u} ℤ)) := by
  let L : SSet.LocalSystem ℤ Y := CategoryTheory.regularPathModuleCoefficientFunctor
    (SSet.FundamentalGroupoid.mk y)
  let Z : ModuleCat.{u} ℤ := ModuleCat.of ℤ (ULift.{u} ℤ)
  let A : ChainComplex (ModuleCat.{u} ℤ) ℕ := SSet.localCoefficientChainComplex (L.pullback f)
  let B : ChainComplex (ModuleCat.{u} ℤ) ℕ := SSet.localCoefficientChainComplex L
  let S : ChainComplex (ModuleCat.{u} ℤ) ℕ :=
    (nativeCoverPullbackSimplexPathGeneratorSSet f y).chainComplex Z
  let T : ChainComplex (ModuleCat.{u} ℤ) ℕ := nativeRegularCoefficientChainComplex Y y Z
  let P : ChainComplex (ModuleCat.{u} ℤ) ℕ :=
    (pullback f (nativeCoverProjection Y y)).chainComplex Z
  let Q : ChainComplex (ModuleCat.{u} ℤ) ℕ := (nativeCover Y y).chainComplex Z
  let M : A ⟶ B := SSet.localCoefficientPullbackChainMap f L
  let eS : A ≅ S := regularLocalCoefficientPullbackGeneratorChainIso f y
  let eT : B ≅ T := originalNativeRegularCoefficientGeneratorChainIso Y y
  let cS : S ≅ P := ((SSet.chainComplexFunctor (ModuleCat.{u} ℤ)).obj Z).mapIso
    (nativeCoverPullbackSimplexPathGeneratorIso f y)
  let cT : T ≅ Q := nativeRegularCoefficientChainCoverIso Y y Z
  let D : S ⟶ T := nativeCoverPullbackRegularCoefficientChainTargetMap f y Z
  let snd : P ⟶ Q := SSet.chainComplexMap (pullback.snd f (nativeCoverProjection Y y)) Z
  have hb : M ≫ eT.hom = eS.hom ≫ D := originalRegularPullbackChainMap_generator_square f y
  have hg : D ≫ cT.hom = cS.hom ≫ snd :=
    nativeCoverPullbackRegularCoefficientChainTargetMap_cover_square f y Z
  have h1 : (M ≫ eT.hom) ≫ cT.hom = (eS.hom ≫ D) ≫ cT.hom :=
    congrArg (fun h : A ⟶ T => h ≫ cT.hom) hb
  have h2 : eS.hom ≫ (D ≫ cT.hom) = eS.hom ≫ (cS.hom ≫ snd) :=
    congrArg (fun h : S ⟶ Q => eS.hom ≫ h) hg
  change M ≫ (eT.hom ≫ cT.hom) = (eS.hom ≫ cS.hom) ≫ snd
  exact (Category.assoc M eT.hom cT.hom).symm.trans
    (h1.trans ((Category.assoc eS.hom D cT.hom).trans
      (h2.trans (Category.assoc eS.hom cS.hom snd).symm)))

/-- The actual homology map of the original coefficient chain map preserves the native square. -/
theorem originalRegularPullbackChainMap_homology_square
    {X Y : SSet.{u}} (f : X ⟶ Y) (y : Y _⦋0⦌) (n : ℕ) :
    let L : SSet.LocalSystem ℤ Y :=
      CategoryTheory.regularPathModuleCoefficientFunctor (SSet.FundamentalGroupoid.mk y)
    HomologicalComplex.homologyMap (SSet.localCoefficientPullbackChainMap f L) n ≫
        HomologicalComplex.homologyMap
          (originalNativeRegularCoefficientCoverChainIso Y y).hom n =
      HomologicalComplex.homologyMap (regularLocalCoefficientPullbackCoverChainIso f y).hom n ≫
        HomologicalComplex.homologyMap
          (SSet.chainComplexMap (pullback.snd f (nativeCoverProjection Y y))
            (ModuleCat.of ℤ (ULift.{u} ℤ))) n := by
  let L : SSet.LocalSystem ℤ Y := CategoryTheory.regularPathModuleCoefficientFunctor
    (SSet.FundamentalGroupoid.mk y)
  let Z : ModuleCat.{u} ℤ := ModuleCat.of ℤ (ULift.{u} ℤ)
  let A : ChainComplex (ModuleCat.{u} ℤ) ℕ := SSet.localCoefficientChainComplex (L.pullback f)
  let B : ChainComplex (ModuleCat.{u} ℤ) ℕ := SSet.localCoefficientChainComplex L
  let P : ChainComplex (ModuleCat.{u} ℤ) ℕ :=
    (pullback f (nativeCoverProjection Y y)).chainComplex Z
  let Q : ChainComplex (ModuleCat.{u} ℤ) ℕ := (nativeCover Y y).chainComplex Z
  let M : A ⟶ B := SSet.localCoefficientPullbackChainMap f L
  let eS : A ≅ P := regularLocalCoefficientPullbackCoverChainIso f y
  let eT : B ≅ Q := originalNativeRegularCoefficientCoverChainIso Y y
  let snd : P ⟶ Q := SSet.chainComplexMap (pullback.snd f (nativeCoverProjection Y y)) Z
  have hs : M ≫ eT.hom = eS.hom ≫ snd := originalRegularPullbackChainMap_cover_square f y
  have h := congrArg (fun h : A ⟶ Q => HomologicalComplex.homologyMap h n) hs
  change HomologicalComplex.homologyMap M n ≫ HomologicalComplex.homologyMap eT.hom n =
    HomologicalComplex.homologyMap eS.hom n ≫ HomologicalComplex.homologyMap snd n
  simpa only [HomologicalComplex.homologyMap_comp] using h

end SSet.KanComplex

namespace SSet.KanComplex

/-- Ordinary inverse loop labels index the actual coefficient arrows at the native basepoint. -/
noncomputable def nativeRegularBasedGroupRingIndexEquiv
    {Y : SSet.{u}} [SSet.KanComplex Y] (y : Y _⦋0⦌) :
    (SSet.FundamentalGroupoid.mk y ⟶ SSet.FundamentalGroupoid.mk y) ≃ π 1 Y y :=
  let ψ := piOneMulEquivFundamentalGroupoidEnd y
  { toFun := fun γ => (ψ.symm (End.of γ))⁻¹
    invFun := fun a => ((ψ a)⁻¹).asHom
    left_inv := by
      intro γ
      change ((ψ ((ψ.symm (End.of γ))⁻¹))⁻¹).asHom = γ
      rw [map_inv, MulEquiv.apply_symm_apply, inv_inv]
    right_inv := by
      intro a
      change (ψ.symm ((ψ a)⁻¹))⁻¹ = a
      rw [map_inv, MulEquiv.symm_apply_apply, inv_inv] }

/-- The actual regular coefficient at the native basepoint is its literal integral group ring. -/
noncomputable def nativeRegularBasedGroupRingIso
    {Y : SSet.{u}} [SSet.KanComplex Y] (y : Y _⦋0⦌) :
    (CategoryTheory.regularPathModuleCoefficientFunctor (SSet.FundamentalGroupoid.mk y)).obj
        (SSet.FundamentalGroupoid.mk y) ≅ ModuleCat.of ℤ (MonoidAlgebra ℤ (π 1 Y y)) := by
  let b := SSet.FundamentalGroupoid.mk y
  let H : Type u := b ⟶ b
  let G : Type u := π 1 Y y
  let e : FreeAbelianGroup H ≃+ (H →₀ ℤ) := FreeAbelianGroup.equivFinsupp H
  let q : FreeAbelianGroup H ≃ₗ[ℤ] (H →₀ ℤ) :=
    e.toLinearEquiv (fun z t => (e.toAddMonoidHom.toIntLinearMap).map_smul z t)
  let d : (H →₀ ℤ) ≃ₗ[ℤ] (G →₀ ℤ) :=
    Finsupp.domLCongr (nativeRegularBasedGroupRingIndexEquiv y)
  let c : MonoidAlgebra ℤ G ≃ₗ[ℤ] (G →₀ ℤ) := MonoidAlgebra.coeffLinearEquiv ℤ
  change ModuleCat.of ℤ (FreeAbelianGroup H) ≅ ModuleCat.of ℤ (MonoidAlgebra ℤ G)
  exact ((q.trans d).trans c.symm).toModuleIso

/-- Every original coefficient path and integer keep their computed ordinary inverse loop label. -/
theorem nativeRegularBasedGroupRingIso_hom_zsmul
    {Y : SSet.{u}} [SSet.KanComplex Y] (y : Y _⦋0⦌)
    (γ : SSet.FundamentalGroupoid.mk y ⟶ SSet.FundamentalGroupoid.mk y) (z : ℤ) :
    (nativeRegularBasedGroupRingIso y).hom (z • FreeAbelianGroup.of γ) =
      MonoidAlgebra.single ((piOneMulEquivFundamentalGroupoidEnd y).symm (End.of γ))⁻¹ z := by
  let b := SSet.FundamentalGroupoid.mk y
  let A : ModuleCat.{u} ℤ := (CategoryTheory.regularPathModuleCoefficientFunctor b).obj b
  let G : Type u := π 1 Y y
  let R : Type u := MonoidAlgebra ℤ G
  let e := nativeRegularBasedGroupRingIso y
  let j : G := nativeRegularBasedGroupRingIndexEquiv y γ
  have h0 : e.hom (FreeAbelianGroup.of γ : A) = MonoidAlgebra.single j (1 : ℤ) := by
    change MonoidAlgebra.ofCoeff
        ((Finsupp.domLCongr (nativeRegularBasedGroupRingIndexEquiv y) :
          ((b ⟶ b) →₀ ℤ) ≃ₗ[ℤ] (G →₀ ℤ))
          (FreeAbelianGroup.toFinsupp (FreeAbelianGroup.of γ))) =
      MonoidAlgebra.single j (1 : ℤ)
    rw [FreeAbelianGroup.toFinsupp_of, Finsupp.domLCongr_single]
    rfl
  have hs : z • (MonoidAlgebra.single j (1 : ℤ) : R) = MonoidAlgebra.single j z :=
    (MonoidAlgebra.smul_single' z j (1 : ℤ)).trans
      (congrArg (MonoidAlgebra.single j) (mul_one z))
  change e.hom (z • (FreeAbelianGroup.of γ : A)) = MonoidAlgebra.single j z
  exact (e.hom.hom.map_smul z (FreeAbelianGroup.of γ : A)).trans
    ((congrArg (fun t : R => z • t) h0).trans hs)

/-- The inverse sends a group-ring basis element to its actual inverse-End coefficient path. -/
theorem nativeRegularBasedGroupRingIso_inv_single
    {Y : SSet.{u}} [SSet.KanComplex Y] (y : Y _⦋0⦌) (a : π 1 Y y) (z : ℤ) :
    (nativeRegularBasedGroupRingIso y).inv (MonoidAlgebra.single a z) =
      z • FreeAbelianGroup.of ((piOneMulEquivFundamentalGroupoidEnd y a)⁻¹).asHom := by
  let b := SSet.FundamentalGroupoid.mk y
  let A : ModuleCat.{u} ℤ := (CategoryTheory.regularPathModuleCoefficientFunctor b).obj b
  let B : ModuleCat.{u} ℤ := ModuleCat.of ℤ (MonoidAlgebra ℤ (π 1 Y y))
  let e := nativeRegularBasedGroupRingIso y
  let ψ := piOneMulEquivFundamentalGroupoidEnd y
  let γ : b ⟶ b := ((ψ a)⁻¹).asHom
  have hj : (ψ.symm (End.of γ))⁻¹ = a :=
    (nativeRegularBasedGroupRingIndexEquiv y).apply_symm_apply a
  have hf : e.hom (z • (FreeAbelianGroup.of γ : A)) = MonoidAlgebra.single a z :=
    (nativeRegularBasedGroupRingIso_hom_zsmul y γ z).trans
      (congrArg (fun g : π 1 Y y => MonoidAlgebra.single g z) hj)
  have hi : e.inv (e.hom (z • (FreeAbelianGroup.of γ : A))) =
      z • (FreeAbelianGroup.of γ : A) :=
    congrArg (fun h : A ⟶ A => h (z • (FreeAbelianGroup.of γ : A))) e.hom_inv_id
  exact (congrArg (fun t : B => e.inv t) hf.symm).trans hi

/-- The actual regular coefficient has the ordinary group-ring integral basis. -/
noncomputable def nativeRegularBasedGroupRingBasis
    {Y : SSet.{u}} [SSet.KanComplex Y] (y : Y _⦋0⦌) :
    Module.Basis (π 1 Y y) ℤ
      ((CategoryTheory.regularPathModuleCoefficientFunctor (SSet.FundamentalGroupoid.mk y)).obj
        (SSet.FundamentalGroupoid.mk y)) :=
  (MonoidAlgebra.basis (π 1 Y y) ℤ).map (nativeRegularBasedGroupRingIso y).toLinearEquiv.symm

/-- The basis vector at a is the original path represented by the inverse of its End label. -/
theorem nativeRegularBasedGroupRingBasis_apply
    {Y : SSet.{u}} [SSet.KanComplex Y] (y : Y _⦋0⦌) (a : π 1 Y y) :
    nativeRegularBasedGroupRingBasis y a =
      FreeAbelianGroup.of ((piOneMulEquivFundamentalGroupoidEnd y a)⁻¹).asHom := by
  let b := SSet.FundamentalGroupoid.mk y
  let A : ModuleCat.{u} ℤ := (CategoryTheory.regularPathModuleCoefficientFunctor b).obj b
  let e := nativeRegularBasedGroupRingIso y
  let γ : b ⟶ b := ((piOneMulEquivFundamentalGroupoidEnd y a)⁻¹).asHom
  have h : e.inv (MonoidAlgebra.single a (1 : ℤ)) = (1 : ℤ) • (FreeAbelianGroup.of γ : A) :=
    nativeRegularBasedGroupRingIso_inv_single y a (1 : ℤ)
  change e.inv (MonoidAlgebra.single a (1 : ℤ)) = (FreeAbelianGroup.of γ : A)
  exact h.trans (one_smul ℤ (FreeAbelianGroup.of γ : A))

/-- Original positive loop transport is right multiplication by the inverse group-ring label. -/
theorem nativeRegularBasedGroupRingIso_postcomp_positive
    {Y : SSet.{u}} [SSet.KanComplex Y] (y : Y _⦋0⦌) (a : π 1 Y y)
    (t : (CategoryTheory.regularPathModuleCoefficientFunctor (SSet.FundamentalGroupoid.mk y)).obj
      (SSet.FundamentalGroupoid.mk y)) :
    (nativeRegularBasedGroupRingIso y).hom
        ((CategoryTheory.regularPathModuleCoefficientFunctor (SSet.FundamentalGroupoid.mk y)).map
          (piOneMulEquivFundamentalGroupoidEnd y a).asHom t) =
      (nativeRegularBasedGroupRingIso y).hom t * MonoidAlgebra.single a⁻¹ (1 : ℤ) := by
  let b := SSet.FundamentalGroupoid.mk y
  let A : ModuleCat.{u} ℤ := (CategoryTheory.regularPathModuleCoefficientFunctor b).obj b
  let R : Type u := MonoidAlgebra ℤ (π 1 Y y)
  let ψ := piOneMulEquivFundamentalGroupoidEnd y
  let e := nativeRegularBasedGroupRingIso y
  let J := nativeRegularBasedGroupRingIndexEquiv y
  let T : A ⟶ A := (CategoryTheory.regularPathModuleCoefficientFunctor b).map (ψ a).asHom
  let fL : A →+ R := e.hom.hom.toAddMonoidHom.comp T.hom.toAddMonoidHom
  let fR : A →+ R := (AddMonoidHom.mulRight (MonoidAlgebra.single a⁻¹ (1 : ℤ))).comp
    e.hom.hom.toAddMonoidHom
  have hpoint : ∀ γ : b ⟶ b,
      e.hom (FreeAbelianGroup.of γ : A) = MonoidAlgebra.single (J γ) (1 : ℤ) := by
    intro γ
    exact (congrArg (fun v : A => e.hom v)
      (one_smul ℤ (FreeAbelianGroup.of γ : A)).symm).trans
        (nativeRegularBasedGroupRingIso_hom_zsmul y γ (1 : ℤ))
  have hmaps : fL = fR := by
    refine FreeAbelianGroup.lift_ext _ _ ?_
    intro γ
    let γ' : b ⟶ b := γ ≫ (ψ a).asHom
    have hT : T (FreeAbelianGroup.of γ : A) = (FreeAbelianGroup.of γ' : A) :=
      CategoryTheory.regularPathModuleCoefficientFunctor_map_of b (ψ a).asHom γ
    have hEnd : End.of γ' = ψ a * End.of γ := rfl
    have hJ : J γ' = J γ * a⁻¹ := by
      change (ψ.symm (End.of γ'))⁻¹ = (ψ.symm (End.of γ))⁻¹ * a⁻¹
      rw [hEnd, map_mul, mul_inv_rev, MulEquiv.symm_apply_apply]
    have hl : e.hom (T (FreeAbelianGroup.of γ : A)) =
        MonoidAlgebra.single (J γ') (1 : ℤ) :=
      (congrArg (fun v : A => e.hom v) hT).trans (hpoint γ')
    have hprod : (MonoidAlgebra.single (J γ) (1 : ℤ) : R) *
          MonoidAlgebra.single a⁻¹ (1 : ℤ) =
        MonoidAlgebra.single (J γ * a⁻¹) (1 : ℤ) := by
      simpa only [one_mul] using
        (MonoidAlgebra.single_mul_single (J γ) a⁻¹ (1 : ℤ) (1 : ℤ))
    have hr : e.hom (FreeAbelianGroup.of γ : A) * MonoidAlgebra.single a⁻¹ (1 : ℤ) =
        MonoidAlgebra.single (J γ * a⁻¹) (1 : ℤ) :=
      (congrArg (fun v : R => v * MonoidAlgebra.single a⁻¹ (1 : ℤ)) (hpoint γ)).trans hprod
    change e.hom (T (FreeAbelianGroup.of γ : A)) =
      e.hom (FreeAbelianGroup.of γ : A) * MonoidAlgebra.single a⁻¹ (1 : ℤ)
    exact (hl.trans (congrArg (fun g : π 1 Y y => MonoidAlgebra.single g (1 : ℤ)) hJ)).trans
      hr.symm
  exact congrArg (fun h : A →+ R => h t) hmaps

/-- Transport by the inverse-End path gamma(a) is right multiplication by the positive label a. -/
theorem nativeRegularBasedGroupRingIso_postcomp_inverse
    {Y : SSet.{u}} [SSet.KanComplex Y] (y : Y _⦋0⦌) (a : π 1 Y y)
    (t : (CategoryTheory.regularPathModuleCoefficientFunctor (SSet.FundamentalGroupoid.mk y)).obj
      (SSet.FundamentalGroupoid.mk y)) :
    (nativeRegularBasedGroupRingIso y).hom
        ((CategoryTheory.regularPathModuleCoefficientFunctor (SSet.FundamentalGroupoid.mk y)).map
          ((piOneMulEquivFundamentalGroupoidEnd y a)⁻¹).asHom t) =
      (nativeRegularBasedGroupRingIso y).hom t * MonoidAlgebra.single a (1 : ℤ) := by
  have h := nativeRegularBasedGroupRingIso_postcomp_positive y a⁻¹ t
  simpa only [map_inv, inv_inv] using h

end SSet.KanComplex

/-!
# Original topological regular coefficients and their singular comparison

The singular comparison identifies actual path bases by full faithfulness.
Its forward map uses the derived basepoint equality and the forward image
of the original path. The source comparison for a topological map includes
the actual singular-pullback coefficient Iso before comparing complexes.
-/

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace SSet

/-- The actual base chain map commutes with a morphism of coefficient systems. -/
theorem localCoefficientPullbackChainMap_coefficient_naturality
    {X Y : SSet.{u}} (f : X ⟶ Y) {L K : SSet.LocalSystem ℤ Y}
    (α : L ⟶ K) :
    SSet.localCoefficientChainMap (Functor.whiskerLeft (SSet.mapFundamentalGroupoid f) α) ≫
        SSet.localCoefficientPullbackChainMap f K =
      SSet.localCoefficientPullbackChainMap f L ≫ SSet.localCoefficientChainMap α := by
  apply HomologicalComplex.hom_ext
  intro n
  let F := SSet.mapFundamentalGroupoid f
  let A : ModuleCat.{u} ℤ := SSet.localCoefficientObj ((SSet.LocalSystem.pullback f L)) n
  let B : ModuleCat.{u} ℤ := SSet.localCoefficientObj ((SSet.LocalSystem.pullback f K)) n
  let C : ModuleCat.{u} ℤ := SSet.localCoefficientObj L n
  let D : ModuleCat.{u} ℤ := SSet.localCoefficientObj K n
  let p : A ⟶ B := (SSet.localCoefficientChainMap (Functor.whiskerLeft F α)).f n
  let mK : B ⟶ D := (SSet.localCoefficientPullbackChainMap f K).f n
  let mL : A ⟶ C := (SSet.localCoefficientPullbackChainMap f L).f n
  let t : C ⟶ D := (SSet.localCoefficientChainMap α).f n
  have hp : p = SSet.localCoefficientMap (Functor.whiskerLeft F α) n :=
    SSet.localCoefficientChainMap_f (Functor.whiskerLeft F α) n
  have ht : t = SSet.localCoefficientMap α n := SSet.localCoefficientChainMap_f α n
  change p ≫ mK = mL ≫ t
  apply Limits.Sigma.hom_ext
  intro s
  let τ : Y _⦋n⦌ := f.app (op ⦋n⦌) s
  let a : SSet.FundamentalGroupoid X :=
    ((SSet.fundamentalGroupoidNerveUnit X).app (op ⦋n⦌) s).left
  let b : SSet.FundamentalGroupoid Y :=
    ((SSet.fundamentalGroupoidNerveUnit Y).app (op ⦋n⦌) τ).left
  let μ : F.obj a = b := (SSet.localCoefficientPullbackLeftIndex f s).symm
  let A0 : ModuleCat.{u} ℤ := SSet.localCoefficientFamily ((SSet.LocalSystem.pullback f L)) n s
  let B0 : ModuleCat.{u} ℤ := SSet.localCoefficientFamily ((SSet.LocalSystem.pullback f K)) n s
  let C0 : ModuleCat.{u} ℤ := SSet.localCoefficientFamily L n τ
  let D0 : ModuleCat.{u} ℤ := SSet.localCoefficientFamily K n τ
  let iA : A0 ⟶ A := SSet.localCoefficientι ((SSet.LocalSystem.pullback f L)) s
  let iB : B0 ⟶ B := SSet.localCoefficientι ((SSet.LocalSystem.pullback f K)) s
  let iC : C0 ⟶ C := SSet.localCoefficientι L τ
  let iD : D0 ⟶ D := SSet.localCoefficientι K τ
  let αA : A0 ⟶ B0 := α.app (F.obj a)
  let αB : C0 ⟶ D0 := α.app b
  let cL : A0 ⟶ C0 := eqToHom (SSet.localCoefficientPullbackFamilyEq f L s)
  let cK : B0 ⟶ D0 := eqToHom (SSet.localCoefficientPullbackFamilyEq f K s)
  have hcast : αA ≫ cK = cL ≫ αB := by
    have hnat : eqToHom (congrArg L.obj μ) ≫ α.app b =
        α.app (F.obj a) ≫ eqToHom (congrArg K.obj μ) := by
      simpa only [eqToHom_map] using α.naturality (eqToHom μ)
    change α.app (F.obj a) ≫ eqToHom (congrArg K.obj μ) =
      eqToHom (congrArg L.obj μ) ≫ α.app b
    exact hnat.symm
  have h1 : iA ≫ p = αA ≫ iB :=
    (congrArg (fun h : A ⟶ B => iA ≫ h) hp).trans
      (SSet.localCoefficientι_map (Functor.whiskerLeft F α) s)
  have h2 : iB ≫ mK = cK ≫ iD :=
    SSet.localCoefficientι_pullbackChainMap f K s
  have h3 : iA ≫ mL = cL ≫ iC :=
    SSet.localCoefficientι_pullbackChainMap f L s
  have h4 : iC ≫ t = αB ≫ iD :=
    (congrArg (fun h : C ⟶ D => iC ≫ h) ht).trans
      (SSet.localCoefficientι_map α τ)
  change iA ≫ (p ≫ mK) = iA ≫ (mL ≫ t)
  calc
    iA ≫ (p ≫ mK) = (iA ≫ p) ≫ mK := (Category.assoc iA p mK).symm
    _ = (αA ≫ iB) ≫ mK := congrArg (fun h : A0 ⟶ B => h ≫ mK) h1
    _ = αA ≫ (iB ≫ mK) := Category.assoc αA iB mK
    _ = αA ≫ (cK ≫ iD) := congrArg (fun h : B0 ⟶ D => αA ≫ h) h2
    _ = (αA ≫ cK) ≫ iD := (Category.assoc αA cK iD).symm
    _ = (cL ≫ αB) ≫ iD := congrArg (fun h : A0 ⟶ D0 => h ≫ iD) hcast
    _ = cL ≫ (αB ≫ iD) := Category.assoc cL αB iD
    _ = cL ≫ (iC ≫ t) := congrArg (fun h : C0 ⟶ D => cL ≫ h) h4.symm
    _ = (cL ≫ iC) ≫ t := (Category.assoc cL iC t).symm
    _ = (iA ≫ mL) ≫ t := congrArg (fun h : A0 ⟶ C => h ≫ t) h3.symm
    _ = iA ≫ (mL ≫ t) := Category.assoc iA mL t

end SSet

namespace TopCat

/-- The singular vertex representing the original point has its actual image. -/
theorem singularRegularBasepoint_eq (Y : TopCat.{u}) (y : Y) :
    (TopCat.singularFundamentalGroupoidFunctor Y).obj
        (SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm y)) =
      _root_.FundamentalGroupoid.mk y :=
  (TopCat.singularFundamentalGroupoidFunctor_obj_mk Y _).trans
    (congrArg _root_.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.apply_symm_apply y))

/-- Full faithfulness and the derived basepoint equality identify actual path types. -/
noncomputable def singularRegularPathEquiv (Y : TopCat.{u}) (y : Y)
    (z : SSet.FundamentalGroupoid (TopCat.toSSet.obj Y)) :
    (SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm y) ⟶ z) ≃
      (_root_.FundamentalGroupoid.mk y ⟶
        (TopCat.singularFundamentalGroupoidFunctor Y).obj z) :=
  ((TopCat.singularFundamentalGroupoidFunctor_fullyFaithful Y).homEquiv
    (X := SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm y)) (Y := z)).trans
    (Iso.homCongr (eqToIso (singularRegularBasepoint_eq Y y))
      (Iso.refl ((TopCat.singularFundamentalGroupoidFunctor Y).obj z)))

/-- The forward path uses the actual comparison, preceded by the basepoint cast. -/
theorem singularRegularPathEquiv_apply (Y : TopCat.{u}) (y : Y)
    (z : SSet.FundamentalGroupoid (TopCat.toSSet.obj Y))
    (γ : SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm y) ⟶ z) :
    singularRegularPathEquiv Y y z γ =
      eqToHom (singularRegularBasepoint_eq Y y).symm ≫
        (TopCat.singularFundamentalGroupoidFunctor Y).map γ := by
  change eqToHom (singularRegularBasepoint_eq Y y).symm ≫
      ((TopCat.singularFundamentalGroupoidFunctor Y).map γ ≫ 𝟙 _) =
    eqToHom (singularRegularBasepoint_eq Y y).symm ≫
      (TopCat.singularFundamentalGroupoidFunctor Y).map γ
  rw [Category.comp_id]

/-- The inverse applies the actual fully faithful preimage after the basepoint cast. -/
theorem singularRegularPathEquiv_symm_apply (Y : TopCat.{u}) (y : Y)
    (z : SSet.FundamentalGroupoid (TopCat.toSSet.obj Y))
    (γ : _root_.FundamentalGroupoid.mk y ⟶
      (TopCat.singularFundamentalGroupoidFunctor Y).obj z) :
    (singularRegularPathEquiv Y y z).symm γ =
      (TopCat.singularFundamentalGroupoidFunctor_fullyFaithful Y).preimage
        (eqToHom (singularRegularBasepoint_eq Y y) ≫ γ) := by
  change (TopCat.singularFundamentalGroupoidFunctor_fullyFaithful Y).preimage
      (eqToHom (singularRegularBasepoint_eq Y y) ≫ (γ ≫ 𝟙 _)) =
    (TopCat.singularFundamentalGroupoidFunctor_fullyFaithful Y).preimage
      (eqToHom (singularRegularBasepoint_eq Y y) ≫ γ)
  rw [Category.comp_id]

/-- The computed path equivalence preserves forward postcomposition. -/
theorem singularRegularPathEquiv_comp (Y : TopCat.{u}) (y : Y)
    {z z' : SSet.FundamentalGroupoid (TopCat.toSSet.obj Y)}
    (γ : SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm y) ⟶ z)
    (q : z ⟶ z') :
    singularRegularPathEquiv Y y z' (γ ≫ q) =
      singularRegularPathEquiv Y y z γ ≫
        (TopCat.singularFundamentalGroupoidFunctor Y).map q := by
  simp only [singularRegularPathEquiv_apply, Functor.map_comp, Category.assoc]

/-- On an edge, the transport is the forward ordinary path represented by that edge. -/
theorem singularRegularPathEquiv_homMk (Y : TopCat.{u}) (y : Y)
    {x z : (TopCat.toSSet.obj Y) _⦋0⦌}
    (γ : SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm y) ⟶
      SSet.FundamentalGroupoid.mk x) (e : (TopCat.toSSet.obj Y).Edge x z) :
    singularRegularPathEquiv Y y (SSet.FundamentalGroupoid.mk z)
        (γ ≫ SSet.FundamentalGroupoid.homMk e) =
      singularRegularPathEquiv Y y (SSet.FundamentalGroupoid.mk x) γ ≫
        Path.Homotopic.Quotient.mk
          ((TopCat.pathEquiv (TopCat.singularEdgePath e)).cast
            (TopCat.counit_realizedVertex x) (TopCat.counit_realizedVertex z)) := by
  exact (singularRegularPathEquiv_comp Y y γ (SSet.FundamentalGroupoid.homMk e)).trans
    (congrArg (fun q : (TopCat.singularFundamentalGroupoidFunctor Y).obj
        (SSet.FundamentalGroupoid.mk x) ⟶
        (TopCat.singularFundamentalGroupoidFunctor Y).obj (SSet.FundamentalGroupoid.mk z) =>
      singularRegularPathEquiv Y y (SSet.FundamentalGroupoid.mk x) γ ≫ q)
      (TopCat.singularFundamentalGroupoidFunctor_map_homMk Y e))

/-- The native regular coefficient system is naturally the original topological system. -/
noncomputable def singularRegularCoefficientIso (Y : TopCat.{u}) (y : Y) :
    CategoryTheory.regularPathModuleCoefficientFunctor
        (SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm y)) ≅
      (TopCat.LocalSystem.toSingular (CategoryTheory.regularPathModuleCoefficientFunctor
        (_root_.FundamentalGroupoid.mk y))) :=
  NatIso.ofComponents
    (F := CategoryTheory.regularPathModuleCoefficientFunctor
      (SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm y)))
    (G := (TopCat.LocalSystem.toSingular (CategoryTheory.regularPathModuleCoefficientFunctor
      (_root_.FundamentalGroupoid.mk y)))) (fun z => by
    let I : Type u := SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm y) ⟶ z
    let J : Type u := _root_.FundamentalGroupoid.mk y ⟶
      (TopCat.singularFundamentalGroupoidFunctor Y).obj z
    let e : FreeAbelianGroup I ≃+ FreeAbelianGroup J :=
      FreeAbelianGroup.equivOfEquiv (singularRegularPathEquiv Y y z)
    let eZ : FreeAbelianGroup I ≃ₗ[ℤ] FreeAbelianGroup J := AddEquiv.toIntLinearEquiv e
    exact LinearEquiv.toModuleIso eZ) (by
    intro z z' q
    apply ModuleCat.hom_ext
    apply LinearMap.toAddMonoidHom_injective
    refine FreeAbelianGroup.lift_ext _ _ ?_
    intro γ
    change FreeAbelianGroup.map (singularRegularPathEquiv Y y z')
        ((CategoryTheory.regularPathModuleCoefficientFunctor
          (SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm y))).map q
            (FreeAbelianGroup.of γ)) =
      (CategoryTheory.regularPathModuleCoefficientFunctor
          (_root_.FundamentalGroupoid.mk y)).map
        ((TopCat.singularFundamentalGroupoidFunctor Y).map q)
          (FreeAbelianGroup.map (singularRegularPathEquiv Y y z) (FreeAbelianGroup.of γ))
    rw [CategoryTheory.regularPathModuleCoefficientFunctor_map_of]
    change FreeAbelianGroup.of (singularRegularPathEquiv Y y z' (γ ≫ q)) =
      (CategoryTheory.regularPathModuleCoefficientFunctor
          (_root_.FundamentalGroupoid.mk y)).map
        ((TopCat.singularFundamentalGroupoidFunctor Y).map q)
          (FreeAbelianGroup.of (singularRegularPathEquiv Y y z γ))
    rw [CategoryTheory.regularPathModuleCoefficientFunctor_map_of]
    exact congrArg FreeAbelianGroup.of (singularRegularPathEquiv_comp Y y γ q))

/-- The forward coefficient comparison sends each basis path to its computed image. -/
theorem singularRegularCoefficientIso_hom_of (Y : TopCat.{u}) (y : Y)
    (z : SSet.FundamentalGroupoid (TopCat.toSSet.obj Y))
    (γ : SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm y) ⟶ z) :
    (singularRegularCoefficientIso Y y).hom.app z (FreeAbelianGroup.of γ) =
      FreeAbelianGroup.of (singularRegularPathEquiv Y y z γ) := by
  change FreeAbelianGroup.map (singularRegularPathEquiv Y y z)
    (FreeAbelianGroup.of γ) = _
  exact FreeAbelianGroup.map_of_apply γ

/-- The inverse coefficient comparison sends each basis path to its actual preimage. -/
theorem singularRegularCoefficientIso_inv_of (Y : TopCat.{u}) (y : Y)
    (z : SSet.FundamentalGroupoid (TopCat.toSSet.obj Y))
    (γ : _root_.FundamentalGroupoid.mk y ⟶
      (TopCat.singularFundamentalGroupoidFunctor Y).obj z) :
    (singularRegularCoefficientIso Y y).inv.app z (FreeAbelianGroup.of γ) =
      FreeAbelianGroup.of ((singularRegularPathEquiv Y y z).symm γ) := by
  change FreeAbelianGroup.map (singularRegularPathEquiv Y y z).symm
    (FreeAbelianGroup.of γ) = _
  exact FreeAbelianGroup.map_of_apply γ

/-- The forward coefficient formula retains the original path and its endpoint cast. -/
theorem singularRegularCoefficientIso_hom_path (Y : TopCat.{u}) (y : Y)
    (z : SSet.FundamentalGroupoid (TopCat.toSSet.obj Y))
    (γ : SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm y) ⟶ z) :
    (singularRegularCoefficientIso Y y).hom.app z (FreeAbelianGroup.of γ) =
      FreeAbelianGroup.of (eqToHom (singularRegularBasepoint_eq Y y).symm ≫
        (TopCat.singularFundamentalGroupoidFunctor Y).map γ) :=
  (singularRegularCoefficientIso_hom_of Y y z γ).trans
    (congrArg FreeAbelianGroup.of (singularRegularPathEquiv_apply Y y z γ))

/-- The inverse coefficient formula uses full faithfulness on the cast original path. -/
theorem singularRegularCoefficientIso_inv_path (Y : TopCat.{u}) (y : Y)
    (z : SSet.FundamentalGroupoid (TopCat.toSSet.obj Y))
    (γ : _root_.FundamentalGroupoid.mk y ⟶
      (TopCat.singularFundamentalGroupoidFunctor Y).obj z) :
    (singularRegularCoefficientIso Y y).inv.app z (FreeAbelianGroup.of γ) =
      FreeAbelianGroup.of
        ((TopCat.singularFundamentalGroupoidFunctor_fullyFaithful Y).preimage
          (eqToHom (singularRegularBasepoint_eq Y y) ≫ γ)) :=
  (singularRegularCoefficientIso_inv_of Y y z γ).trans
    (congrArg FreeAbelianGroup.of (singularRegularPathEquiv_symm_apply Y y z γ))

/-- Every integral coefficient is retained by the inverse path comparison. -/
theorem singularRegularCoefficientIso_inv_smul_of (Y : TopCat.{u}) (y : Y)
    (z : SSet.FundamentalGroupoid (TopCat.toSSet.obj Y))
    (γ : _root_.FundamentalGroupoid.mk y ⟶
      (TopCat.singularFundamentalGroupoidFunctor Y).obj z) (k : ℤ) :
    (singularRegularCoefficientIso Y y).inv.app z (k • FreeAbelianGroup.of γ) =
      k • FreeAbelianGroup.of ((singularRegularPathEquiv Y y z).symm γ) := by
  let K : SSet.LocalSystem ℤ (TopCat.toSSet.obj Y) :=
    CategoryTheory.regularPathModuleCoefficientFunctor
      (SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm y))
  let L : TopCat.LocalSystem ℤ Y :=
    CategoryTheory.regularPathModuleCoefficientFunctor (_root_.FundamentalGroupoid.mk y)
  let A : ModuleCat.{u} ℤ := K.obj z
  let B : ModuleCat.{u} ℤ := (TopCat.LocalSystem.toSingular L).obj z
  let h : B ⟶ A := (singularRegularCoefficientIso Y y).inv.app z
  let γS := (singularRegularPathEquiv Y y z).symm γ
  have hh : h (FreeAbelianGroup.of γ : B) = (FreeAbelianGroup.of γS : A) :=
    singularRegularCoefficientIso_inv_of Y y z γ
  change h (k • (FreeAbelianGroup.of γ : B)) = k • (FreeAbelianGroup.of γS : A)
  exact (h.hom.map_smul k (FreeAbelianGroup.of γ : B)).trans
    (congrArg (fun t : A => k • t) hh)

/-- The actual coefficient-chain functor gives the singular/topological chain Iso. -/
noncomputable def singularRegularCoefficientChainIso (Y : TopCat.{u}) (y : Y) :
    SSet.localCoefficientChainComplex (CategoryTheory.regularPathModuleCoefficientFunctor
        (SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm y))) ≅
      TopCat.localCoefficientChainComplex (CategoryTheory.regularPathModuleCoefficientFunctor
        (_root_.FundamentalGroupoid.mk y)) :=
  (SSet.localCoefficientChainComplexFunctor (R := ℤ) (X := TopCat.toSSet.obj Y)).mapIso
    (singularRegularCoefficientIso Y y)

/-- The forward degree map is the actual coefficient coproduct map. -/
theorem singularRegularCoefficientChainIso_hom_f (Y : TopCat.{u}) (y : Y) (n : ℕ) :
    (singularRegularCoefficientChainIso Y y).hom.f n =
      SSet.localCoefficientMap (singularRegularCoefficientIso Y y).hom n :=
  SSet.localCoefficientChainMap_f (singularRegularCoefficientIso Y y).hom n

/-- The inverse degree map is the actual inverse coefficient coproduct map. -/
theorem singularRegularCoefficientChainIso_inv_f (Y : TopCat.{u}) (y : Y) (n : ℕ) :
    (singularRegularCoefficientChainIso Y y).inv.f n =
      SSet.localCoefficientMap (singularRegularCoefficientIso Y y).inv n :=
  SSet.localCoefficientChainMap_f (singularRegularCoefficientIso Y y).inv n

/-- The forward singular-pullback component is the actual topological path transport. -/
theorem singularPullbackIso_hom_app {X Y : TopCat.{u}} (f : X ⟶ Y)
    (L : TopCat.LocalSystem ℤ Y) (z : SSet.FundamentalGroupoid (TopCat.toSSet.obj X)) :
    (TopCat.LocalSystem.singularPullbackIso f L).hom.app z =
      L.map ((TopCat.singularFundamentalGroupoidNaturality f).hom.app z) := by
  change (𝟙 _) ≫
    (L.map ((TopCat.singularFundamentalGroupoidNaturality f).hom.app z) ≫ (𝟙 _)) = _
  simp only [Category.id_comp, Category.comp_id]

/-- The inverse singular-pullback component is the actual inverse path transport. -/
theorem singularPullbackIso_inv_app {X Y : TopCat.{u}} (f : X ⟶ Y)
    (L : TopCat.LocalSystem ℤ Y) (z : SSet.FundamentalGroupoid (TopCat.toSSet.obj X)) :
    (TopCat.LocalSystem.singularPullbackIso f L).inv.app z =
      L.map ((TopCat.singularFundamentalGroupoidNaturality f).inv.app z) := by
  change ((𝟙 _) ≫ L.map ((TopCat.singularFundamentalGroupoidNaturality f).inv.app z)) ≫
    (𝟙 _) = _
  simp only [Category.id_comp, Category.comp_id]

/-- Source coefficients are aligned through the actual singular-pullback Iso. -/
noncomputable def singularRegularPullbackCoefficientIso {X Y : TopCat.{u}}
    (f : X ⟶ Y) (y : Y) :
    (SSet.LocalSystem.pullback (TopCat.toSSet.map f)
      (CategoryTheory.regularPathModuleCoefficientFunctor
        (SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm y)))) ≅
      (TopCat.LocalSystem.toSingular ((TopCat.LocalSystem.pullback f
        (CategoryTheory.regularPathModuleCoefficientFunctor
        (_root_.FundamentalGroupoid.mk y))))) :=
  Functor.isoWhiskerLeft (SSet.mapFundamentalGroupoid (TopCat.toSSet.map f))
      (singularRegularCoefficientIso Y y) ≪≫
    TopCat.LocalSystem.singularPullbackIso f
      (CategoryTheory.regularPathModuleCoefficientFunctor (_root_.FundamentalGroupoid.mk y))

/-- The source forward map includes the original singular-pullback component. -/
theorem singularRegularPullbackCoefficientIso_hom_app {X Y : TopCat.{u}}
    (f : X ⟶ Y) (y : Y) (z : SSet.FundamentalGroupoid (TopCat.toSSet.obj X)) :
    (singularRegularPullbackCoefficientIso f y).hom.app z =
      (singularRegularCoefficientIso Y y).hom.app
          ((SSet.mapFundamentalGroupoid (TopCat.toSSet.map f)).obj z) ≫
        (TopCat.LocalSystem.singularPullbackIso f
          (CategoryTheory.regularPathModuleCoefficientFunctor
            (_root_.FundamentalGroupoid.mk y))).hom.app z := rfl

/-- The source inverse first uses the actual inverse singular-pullback component. -/
theorem singularRegularPullbackCoefficientIso_inv_app {X Y : TopCat.{u}}
    (f : X ⟶ Y) (y : Y) (z : SSet.FundamentalGroupoid (TopCat.toSSet.obj X)) :
    (singularRegularPullbackCoefficientIso f y).inv.app z =
      (TopCat.LocalSystem.singularPullbackIso f
          (CategoryTheory.regularPathModuleCoefficientFunctor
            (_root_.FundamentalGroupoid.mk y))).inv.app z ≫
        (singularRegularCoefficientIso Y y).inv.app
          ((SSet.mapFundamentalGroupoid (TopCat.toSSet.map f)).obj z) := rfl

/-- Each native source path maps to its actual forward topological source path. -/
theorem singularRegularPullbackCoefficientIso_hom_of {X Y : TopCat.{u}}
    (f : X ⟶ Y) (y : Y) (z : SSet.FundamentalGroupoid (TopCat.toSSet.obj X))
    (γ : SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm y) ⟶
      (SSet.mapFundamentalGroupoid (TopCat.toSSet.map f)).obj z) :
    (singularRegularPullbackCoefficientIso f y).hom.app z (FreeAbelianGroup.of γ) =
      FreeAbelianGroup.of
        (singularRegularPathEquiv Y y
            ((SSet.mapFundamentalGroupoid (TopCat.toSSet.map f)).obj z) γ ≫
          (TopCat.singularFundamentalGroupoidNaturality f).hom.app z) := by
  let F := SSet.mapFundamentalGroupoid (TopCat.toSSet.map f)
  let L : TopCat.LocalSystem ℤ Y := CategoryTheory.regularPathModuleCoefficientFunctor
    (_root_.FundamentalGroupoid.mk y)
  let A : ModuleCat.{u} ℤ :=
    ((SSet.LocalSystem.pullback (TopCat.toSSet.map f)
      (CategoryTheory.regularPathModuleCoefficientFunctor
      (SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm y))))).obj z
  let C : ModuleCat.{u} ℤ :=
    ((SSet.LocalSystem.pullback (TopCat.toSSet.map f) (TopCat.LocalSystem.toSingular L))).obj z
  let B : ModuleCat.{u} ℤ := (TopCat.LocalSystem.toSingular (TopCat.LocalSystem.pullback f L)).obj z
  let e : A ⟶ C := (singularRegularCoefficientIso Y y).hom.app (F.obj z)
  let d : C ⟶ B := L.map ((TopCat.singularFundamentalGroupoidNaturality f).hom.app z)
  have h : (singularRegularPullbackCoefficientIso f y).hom.app z = e ≫ d :=
    (singularRegularPullbackCoefficientIso_hom_app f y z).trans
      (congrArg (fun h : C ⟶ B => e ≫ h) (singularPullbackIso_hom_app f L z))
  have hv : (singularRegularPullbackCoefficientIso f y).hom.app z
      (FreeAbelianGroup.of γ) = d (e (FreeAbelianGroup.of γ)) :=
    congrArg (fun h : A ⟶ B => h (FreeAbelianGroup.of γ)) h
  have he : e (FreeAbelianGroup.of γ) =
      FreeAbelianGroup.of (singularRegularPathEquiv Y y (F.obj z) γ) :=
    singularRegularCoefficientIso_hom_of Y y (F.obj z) γ
  have hd : d (FreeAbelianGroup.of (singularRegularPathEquiv Y y (F.obj z) γ)) =
      FreeAbelianGroup.of (singularRegularPathEquiv Y y (F.obj z) γ ≫
        (TopCat.singularFundamentalGroupoidNaturality f).hom.app z) :=
    CategoryTheory.regularPathModuleCoefficientFunctor_map_of
      (_root_.FundamentalGroupoid.mk y)
      ((TopCat.singularFundamentalGroupoidNaturality f).hom.app z) _
  exact hv.trans ((congrArg (fun v : C => d v) he).trans hd)

/-- Each original source path has its actual singular preimage after inverse alignment. -/
theorem singularRegularPullbackCoefficientIso_inv_of {X Y : TopCat.{u}}
    (f : X ⟶ Y) (y : Y) (z : SSet.FundamentalGroupoid (TopCat.toSSet.obj X))
    (γ : _root_.FundamentalGroupoid.mk y ⟶
      (_root_.FundamentalGroupoid.map f.hom).obj
        ((TopCat.singularFundamentalGroupoidFunctor X).obj z)) :
    (singularRegularPullbackCoefficientIso f y).inv.app z (FreeAbelianGroup.of γ) =
      FreeAbelianGroup.of
        ((singularRegularPathEquiv Y y
            ((SSet.mapFundamentalGroupoid (TopCat.toSSet.map f)).obj z)).symm
          (γ ≫ (TopCat.singularFundamentalGroupoidNaturality f).inv.app z)) := by
  let F := SSet.mapFundamentalGroupoid (TopCat.toSSet.map f)
  let L : TopCat.LocalSystem ℤ Y := CategoryTheory.regularPathModuleCoefficientFunctor
    (_root_.FundamentalGroupoid.mk y)
  let A : ModuleCat.{u} ℤ := (TopCat.LocalSystem.toSingular (TopCat.LocalSystem.pullback f L)).obj z
  let C : ModuleCat.{u} ℤ :=
    ((SSet.LocalSystem.pullback (TopCat.toSSet.map f) (TopCat.LocalSystem.toSingular L))).obj z
  let B : ModuleCat.{u} ℤ :=
    ((SSet.LocalSystem.pullback (TopCat.toSSet.map f)
      (CategoryTheory.regularPathModuleCoefficientFunctor
      (SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm y))))).obj z
  let d : A ⟶ C := L.map ((TopCat.singularFundamentalGroupoidNaturality f).inv.app z)
  let e : C ⟶ B := (singularRegularCoefficientIso Y y).inv.app (F.obj z)
  have h : (singularRegularPullbackCoefficientIso f y).inv.app z = d ≫ e :=
    (singularRegularPullbackCoefficientIso_inv_app f y z).trans
      (congrArg (fun h : A ⟶ C => h ≫ e) (singularPullbackIso_inv_app f L z))
  have hv : (singularRegularPullbackCoefficientIso f y).inv.app z
      (FreeAbelianGroup.of γ) = e (d (FreeAbelianGroup.of γ)) :=
    congrArg (fun h : A ⟶ B => h (FreeAbelianGroup.of γ)) h
  have hd : d (FreeAbelianGroup.of γ) =
      FreeAbelianGroup.of
        (γ ≫ (TopCat.singularFundamentalGroupoidNaturality f).inv.app z) :=
    CategoryTheory.regularPathModuleCoefficientFunctor_map_of
      (_root_.FundamentalGroupoid.mk y)
      ((TopCat.singularFundamentalGroupoidNaturality f).inv.app z) γ
  have he : e (FreeAbelianGroup.of
        (γ ≫ (TopCat.singularFundamentalGroupoidNaturality f).inv.app z)) =
      FreeAbelianGroup.of
        ((singularRegularPathEquiv Y y (F.obj z)).symm
          (γ ≫ (TopCat.singularFundamentalGroupoidNaturality f).inv.app z)) :=
    singularRegularCoefficientIso_inv_of Y y (F.obj z) _
  exact hv.trans ((congrArg (fun v : C => e v) hd).trans he)

/-- Inverse source alignment retains every integral coefficient on its actual path. -/
theorem singularRegularPullbackCoefficientIso_inv_smul_of {X Y : TopCat.{u}}
    (f : X ⟶ Y) (y : Y) (z : SSet.FundamentalGroupoid (TopCat.toSSet.obj X))
    (γ : _root_.FundamentalGroupoid.mk y ⟶
      (_root_.FundamentalGroupoid.map f.hom).obj
        ((TopCat.singularFundamentalGroupoidFunctor X).obj z)) (k : ℤ) :
    (singularRegularPullbackCoefficientIso f y).inv.app z (k • FreeAbelianGroup.of γ) =
      k • FreeAbelianGroup.of
        ((singularRegularPathEquiv Y y
            ((SSet.mapFundamentalGroupoid (TopCat.toSSet.map f)).obj z)).symm
          (γ ≫ (TopCat.singularFundamentalGroupoidNaturality f).inv.app z)) := by
  let F := SSet.mapFundamentalGroupoid (TopCat.toSSet.map f)
  let K : SSet.LocalSystem ℤ (TopCat.toSSet.obj Y) :=
    CategoryTheory.regularPathModuleCoefficientFunctor
      (SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm y))
  let L : TopCat.LocalSystem ℤ Y :=
    CategoryTheory.regularPathModuleCoefficientFunctor (_root_.FundamentalGroupoid.mk y)
  let A : ModuleCat.{u} ℤ := (SSet.LocalSystem.pullback (TopCat.toSSet.map f) K).obj z
  let B : ModuleCat.{u} ℤ :=
    (TopCat.LocalSystem.toSingular (TopCat.LocalSystem.pullback f L)).obj z
  let h : B ⟶ A := (singularRegularPullbackCoefficientIso f y).inv.app z
  let γS := (singularRegularPathEquiv Y y (F.obj z)).symm
    (γ ≫ (TopCat.singularFundamentalGroupoidNaturality f).inv.app z)
  have hh : h (FreeAbelianGroup.of γ : B) = (FreeAbelianGroup.of γS : A) :=
    singularRegularPullbackCoefficientIso_inv_of f y z γ
  change h (k • (FreeAbelianGroup.of γ : B)) = k • (FreeAbelianGroup.of γS : A)
  exact (h.hom.map_smul k (FreeAbelianGroup.of γ : B)).trans
    (congrArg (fun t : A => k • t) hh)

/-- The actual coefficient functor identifies native source chains with original TopCat chains. -/
noncomputable def singularRegularPullbackCoefficientChainIso {X Y : TopCat.{u}}
    (f : X ⟶ Y) (y : Y) :
    SSet.localCoefficientChainComplex
        ((SSet.LocalSystem.pullback (TopCat.toSSet.map f)
          (CategoryTheory.regularPathModuleCoefficientFunctor
          (SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm y))))) ≅
      TopCat.localCoefficientChainComplex
        ((TopCat.LocalSystem.pullback f (CategoryTheory.regularPathModuleCoefficientFunctor
          (_root_.FundamentalGroupoid.mk y)))) :=
  (SSet.localCoefficientChainComplexFunctor (R := ℤ) (X := TopCat.toSSet.obj X)).mapIso
    (singularRegularPullbackCoefficientIso f y)

/-- Inverse source degree maps are the original coefficient coproduct maps. -/
theorem singularRegularPullbackCoefficientChainIso_inv_f {X Y : TopCat.{u}}
    (f : X ⟶ Y) (y : Y) (n : ℕ) :
    (singularRegularPullbackCoefficientChainIso f y).inv.f n =
      SSet.localCoefficientMap (singularRegularPullbackCoefficientIso f y).inv n :=
  SSet.localCoefficientChainMap_f (singularRegularPullbackCoefficientIso f y).inv n

/-- The literal original TopCat map has the actual singular native regular chain square. -/
theorem originalTopRegularCoefficientChainMap_square {X Y : TopCat.{u}}
    (f : X ⟶ Y) (y : Y) :
    TopCat.localCoefficientPullbackChainMap f
        (CategoryTheory.regularPathModuleCoefficientFunctor (_root_.FundamentalGroupoid.mk y)) ≫
      (singularRegularCoefficientChainIso Y y).inv =
        (singularRegularPullbackCoefficientChainIso f y).inv ≫
          SSet.localCoefficientPullbackChainMap (TopCat.toSSet.map f)
            (CategoryTheory.regularPathModuleCoefficientFunctor
              (SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm y))) := by
  let sf := TopCat.toSSet.map f
  let F := SSet.mapFundamentalGroupoid sf
  let K : SSet.LocalSystem ℤ (TopCat.toSSet.obj Y) :=
    CategoryTheory.regularPathModuleCoefficientFunctor
      (SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm y))
  let L : TopCat.LocalSystem ℤ Y := CategoryTheory.regularPathModuleCoefficientFunctor
    (_root_.FundamentalGroupoid.mk y)
  let δ := TopCat.LocalSystem.singularPullbackIso f L
  let ε := singularRegularCoefficientIso Y y
  let A : ChainComplex (ModuleCat.{u} ℤ) ℕ :=
    TopCat.localCoefficientChainComplex ((TopCat.LocalSystem.pullback f L))
  let C : ChainComplex (ModuleCat.{u} ℤ) ℕ :=
    SSet.localCoefficientChainComplex ((SSet.LocalSystem.pullback sf
      (TopCat.LocalSystem.toSingular L)))
  let B : ChainComplex (ModuleCat.{u} ℤ) ℕ := TopCat.localCoefficientChainComplex L
  let P : ChainComplex (ModuleCat.{u} ℤ) ℕ :=
    SSet.localCoefficientChainComplex ((SSet.LocalSystem.pullback sf K))
  let Q : ChainComplex (ModuleCat.{u} ℤ) ℕ := SSet.localCoefficientChainComplex K
  let d : A ⟶ C := SSet.localCoefficientChainMap δ.inv
  let p : C ⟶ P := SSet.localCoefficientChainMap (Functor.whiskerLeft F ε.inv)
  let t : B ⟶ Q := SSet.localCoefficientChainMap ε.inv
  let mL : C ⟶ B := SSet.localCoefficientPullbackChainMap sf (TopCat.LocalSystem.toSingular L)
  let mK : P ⟶ Q := SSet.localCoefficientPullbackChainMap sf K
  let M : A ⟶ B := TopCat.localCoefficientPullbackChainMap f L
  let eS : P ≅ A := singularRegularPullbackCoefficientChainIso f y
  let eT : Q ≅ B := singularRegularCoefficientChainIso Y y
  have hM : M = d ≫ mL := rfl
  have hT : eT.inv = t := rfl
  have hI : (singularRegularPullbackCoefficientIso f y).inv =
      δ.inv ≫ Functor.whiskerLeft F ε.inv := rfl
  have hS : eS.inv = d ≫ p := by
    change SSet.localCoefficientChainMap
        (singularRegularPullbackCoefficientIso f y).inv = d ≫ p
    exact (congrArg (fun α : (TopCat.LocalSystem.toSingular (TopCat.LocalSystem.pullback f L)) ⟶
      (SSet.LocalSystem.pullback sf K) =>
      SSet.localCoefficientChainMap α) hI).trans
        (SSet.localCoefficientChainMap_comp δ.inv (Functor.whiskerLeft F ε.inv))
  have hbase : p ≫ mK = mL ≫ t :=
    SSet.localCoefficientPullbackChainMap_coefficient_naturality sf ε.inv
  change M ≫ eT.inv = eS.inv ≫ mK
  calc
    M ≫ eT.inv = (d ≫ mL) ≫ t := by rw [hM, hT]
    _ = d ≫ (mL ≫ t) := Category.assoc d mL t
    _ = d ≫ (p ≫ mK) := congrArg (fun h : C ⟶ Q => d ≫ h) hbase.symm
    _ = (d ≫ p) ≫ mK := (Category.assoc d p mK).symm
    _ = eS.inv ≫ mK := congrArg (fun h : A ⟶ P => h ≫ mK) hS.symm

/-- The original topological regular complex identifies with the established native cover chains. -/
noncomputable def originalTopRegularCoverChainIso (Y : TopCat.{u}) (y : Y) :
    TopCat.localCoefficientChainComplex (CategoryTheory.regularPathModuleCoefficientFunctor
        (_root_.FundamentalGroupoid.mk y)) ≅
      SSet.chainComplex
        (SSet.KanComplex.nativeCover (TopCat.toSSet.obj Y) (TopCat.toSSetObj₀Equiv.symm y))
        (ModuleCat.of ℤ (ULift.{u} ℤ)) :=
  (singularRegularCoefficientChainIso Y y).symm ≪≫
    SSet.KanComplex.originalNativeRegularCoefficientCoverChainIso
      (TopCat.toSSet.obj Y) (TopCat.toSSetObj₀Equiv.symm y)

/-- Original topological pullback coefficients identify with the literal
pulled-back cover chains. -/
noncomputable def originalTopRegularPullbackCoverChainIso {X Y : TopCat.{u}}
    (f : X ⟶ Y) (y : Y) :
    TopCat.localCoefficientChainComplex
        ((TopCat.LocalSystem.pullback f (CategoryTheory.regularPathModuleCoefficientFunctor
          (_root_.FundamentalGroupoid.mk y)))) ≅
      (pullback (TopCat.toSSet.map f)
        (SSet.KanComplex.nativeCoverProjection (TopCat.toSSet.obj Y)
          (TopCat.toSSetObj₀Equiv.symm y))).chainComplex (ModuleCat.of ℤ (ULift.{u} ℤ)) :=
  (singularRegularPullbackCoefficientChainIso f y).symm ≪≫
    SSet.KanComplex.regularLocalCoefficientPullbackCoverChainIso
      (TopCat.toSSet.map f) (TopCat.toSSetObj₀Equiv.symm y)

/-- The original topological comparison preserves every integer on each actual path generator. -/
theorem originalTopRegularCoverChainIso_hom_ι_basis
    (Y : TopCat.{u}) (y : Y) (n : ℕ) (s : (TopCat.toSSet.obj Y) _⦋n⦌)
    (γ : _root_.FundamentalGroupoid.mk y ⟶
      (TopCat.singularFundamentalGroupoidFunctor Y).obj (ComposableArrows.left
        ((SSet.fundamentalGroupoidNerveUnit (TopCat.toSSet.obj Y)).app (op ⦋n⦌) s)))
    (k : ℤ) :
    (originalTopRegularCoverChainIso Y y).hom.f n
        (SSet.localCoefficientι
          (TopCat.LocalSystem.toSingular (CategoryTheory.regularPathModuleCoefficientFunctor
            (_root_.FundamentalGroupoid.mk y))) s (k • FreeAbelianGroup.of γ)) =
      SSet.ιChainComplex
        (SSet.KanComplex.nativeCover (TopCat.toSSet.obj Y) (TopCat.toSSetObj₀Equiv.symm y))
        (R := ModuleCat.of ℤ (ULift.{u} ℤ))
          (SSet.KanComplex.nativeCoverSimplexPathGeneratorsEquiv
            (TopCat.toSSet.obj Y) (TopCat.toSSetObj₀Equiv.symm y) n
            (SSet.KanComplex.regularLocalCoefficientPathIndexEquiv
              (𝟭 (SSet.FundamentalGroupoid (TopCat.toSSet.obj Y)))
              (SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm y)) n
              ⟨s, (singularRegularPathEquiv Y y (ComposableArrows.left
                ((SSet.fundamentalGroupoidNerveUnit (TopCat.toSSet.obj Y)).app
                  (op ⦋n⦌) s))).symm γ⟩)) (ULift.up k) := by
  let S := TopCat.toSSet.obj Y
  let ys : S _⦋0⦌ := TopCat.toSSetObj₀Equiv.symm y
  let a : SSet.FundamentalGroupoid S :=
    ((SSet.fundamentalGroupoidNerveUnit S).app (op ⦋n⦌) s).left
  let K : SSet.LocalSystem ℤ S := CategoryTheory.regularPathModuleCoefficientFunctor
    (SSet.FundamentalGroupoid.mk ys)
  let L : TopCat.LocalSystem ℤ Y := CategoryTheory.regularPathModuleCoefficientFunctor
    (_root_.FundamentalGroupoid.mk y)
  let A0 : ModuleCat.{u} ℤ := SSet.localCoefficientFamily (TopCat.LocalSystem.toSingular L) n s
  let B0 : ModuleCat.{u} ℤ := SSet.localCoefficientFamily K n s
  let A : ModuleCat.{u} ℤ := SSet.localCoefficientObj (TopCat.LocalSystem.toSingular L) n
  let B : ModuleCat.{u} ℤ := SSet.localCoefficientObj K n
  let H : A ⟶ B := (singularRegularCoefficientChainIso Y y).inv.f n
  let iA : A0 ⟶ A := SSet.localCoefficientι (TopCat.LocalSystem.toSingular L) s
  let iB : B0 ⟶ B := SSet.localCoefficientι K s
  let γS : SSet.FundamentalGroupoid.mk ys ⟶ a := (singularRegularPathEquiv Y y a).symm γ
  have hH : H = SSet.localCoefficientMap (singularRegularCoefficientIso Y y).inv n :=
    singularRegularCoefficientChainIso_inv_f Y y n
  have hi : iA ≫ H = (singularRegularCoefficientIso Y y).inv.app a ≫ iB :=
    (congrArg (fun h : A ⟶ B => iA ≫ h) hH).trans
      (SSet.localCoefficientι_map (singularRegularCoefficientIso Y y).inv s)
  have hv : H (iA (k • FreeAbelianGroup.of γ)) =
      iB ((singularRegularCoefficientIso Y y).inv.app a (k • FreeAbelianGroup.of γ)) :=
    congrArg (fun h : A0 ⟶ B => h (k • FreeAbelianGroup.of γ)) hi
  have hc : H (iA (k • FreeAbelianGroup.of γ)) =
      iB (k • FreeAbelianGroup.of γS) :=
    hv.trans (congrArg (fun v : B0 => iB v)
      (singularRegularCoefficientIso_inv_smul_of Y y a γ k))
  let Z : ModuleCat.{u} ℤ := ModuleCat.of ℤ (ULift.{u} ℤ)
  let W : SSet.{u} := SSet.KanComplex.nativeCover S ys
  let e : SSet.localCoefficientChainComplex K ≅ W.chainComplex Z :=
    SSet.KanComplex.originalNativeRegularCoefficientCoverChainIso S ys
  have h0 := SSet.KanComplex.originalNativeRegularCoefficientCoverChainIso_hom_ι_basis
    S ys n s γS k
  change e.hom.f n (H (iA (k • FreeAbelianGroup.of γ))) = _
  exact (congrArg (fun v : B => e.hom.f n v) hc).trans h0

/-- The pullback comparison preserves every integer and the actual inverse source alignment. -/
theorem originalTopRegularPullbackCoverChainIso_hom_ι_basis {X Y : TopCat.{u}}
    (f : X ⟶ Y) (y : Y) (n : ℕ) (s : (TopCat.toSSet.obj X) _⦋n⦌)
    (γ : _root_.FundamentalGroupoid.mk y ⟶
      (_root_.FundamentalGroupoid.map f.hom).obj
        ((TopCat.singularFundamentalGroupoidFunctor X).obj (ComposableArrows.left
          ((SSet.fundamentalGroupoidNerveUnit (TopCat.toSSet.obj X)).app (op ⦋n⦌) s))))
    (k : ℤ) :
    (originalTopRegularPullbackCoverChainIso f y).hom.f n
        (SSet.localCoefficientι
          (TopCat.LocalSystem.toSingular ((TopCat.LocalSystem.pullback f
            (CategoryTheory.regularPathModuleCoefficientFunctor
            (_root_.FundamentalGroupoid.mk y))))) s
          (k • FreeAbelianGroup.of γ)) =
      (pullback (TopCat.toSSet.map f)
        (SSet.KanComplex.nativeCoverProjection (TopCat.toSSet.obj Y)
          (TopCat.toSSetObj₀Equiv.symm y))).ιChainComplex
        (R := ModuleCat.of ℤ (ULift.{u} ℤ))
        (SSet.KanComplex.nativeCoverPullbackSimplexPathGeneratorsEquiv
          (TopCat.toSSet.map f) (TopCat.toSSetObj₀Equiv.symm y) n
          (SSet.KanComplex.regularLocalCoefficientPullbackPathIndexEquiv
            (TopCat.toSSet.map f) (TopCat.toSSetObj₀Equiv.symm y) n
            (SSet.KanComplex.regularLocalCoefficientPathIndexEquiv
              (SSet.mapFundamentalGroupoid (TopCat.toSSet.map f))
              (SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm y)) n
              ⟨s, (singularRegularPathEquiv Y y
                ((SSet.mapFundamentalGroupoid (TopCat.toSSet.map f)).obj
                  (ComposableArrows.left
                    ((SSet.fundamentalGroupoidNerveUnit (TopCat.toSSet.obj X)).app
                      (op ⦋n⦌) s)))).symm
                    (γ ≫ (TopCat.singularFundamentalGroupoidNaturality f).inv.app
                      (ComposableArrows.left
                        ((SSet.fundamentalGroupoidNerveUnit (TopCat.toSSet.obj X)).app
                          (op ⦋n⦌) s)))⟩))) (ULift.up k) := by
  let SX := TopCat.toSSet.obj X
  let SY := TopCat.toSSet.obj Y
  let sf := TopCat.toSSet.map f
  let F := SSet.mapFundamentalGroupoid sf
  let ys : SY _⦋0⦌ := TopCat.toSSetObj₀Equiv.symm y
  let a : SSet.FundamentalGroupoid SX :=
    ((SSet.fundamentalGroupoidNerveUnit SX).app (op ⦋n⦌) s).left
  let K : SSet.LocalSystem ℤ SY := CategoryTheory.regularPathModuleCoefficientFunctor
    (SSet.FundamentalGroupoid.mk ys)
  let L : TopCat.LocalSystem ℤ Y := CategoryTheory.regularPathModuleCoefficientFunctor
    (_root_.FundamentalGroupoid.mk y)
  let A0 : ModuleCat.{u} ℤ :=
    SSet.localCoefficientFamily
      (TopCat.LocalSystem.toSingular (TopCat.LocalSystem.pullback f L)) n s
  let B0 : ModuleCat.{u} ℤ := SSet.localCoefficientFamily ((SSet.LocalSystem.pullback sf K)) n s
  let A : ModuleCat.{u} ℤ :=
    SSet.localCoefficientObj (TopCat.LocalSystem.toSingular (TopCat.LocalSystem.pullback f L)) n
  let B : ModuleCat.{u} ℤ := SSet.localCoefficientObj ((SSet.LocalSystem.pullback sf K)) n
  let H : A ⟶ B := (singularRegularPullbackCoefficientChainIso f y).inv.f n
  let iA : A0 ⟶ A :=
    SSet.localCoefficientι (TopCat.LocalSystem.toSingular (TopCat.LocalSystem.pullback f L)) s
  let iB : B0 ⟶ B := SSet.localCoefficientι ((SSet.LocalSystem.pullback sf K)) s
  let γS : SSet.FundamentalGroupoid.mk ys ⟶ F.obj a :=
    (singularRegularPathEquiv Y y (F.obj a)).symm
      (γ ≫ (TopCat.singularFundamentalGroupoidNaturality f).inv.app a)
  have hH : H = SSet.localCoefficientMap
      (singularRegularPullbackCoefficientIso f y).inv n :=
    singularRegularPullbackCoefficientChainIso_inv_f f y n
  have hi : iA ≫ H = (singularRegularPullbackCoefficientIso f y).inv.app a ≫ iB :=
    (congrArg (fun h : A ⟶ B => iA ≫ h) hH).trans
      (SSet.localCoefficientι_map (singularRegularPullbackCoefficientIso f y).inv s)
  have hv : H (iA (k • FreeAbelianGroup.of γ)) =
      iB ((singularRegularPullbackCoefficientIso f y).inv.app a
        (k • FreeAbelianGroup.of γ)) :=
    congrArg (fun h : A0 ⟶ B => h (k • FreeAbelianGroup.of γ)) hi
  have hc : H (iA (k • FreeAbelianGroup.of γ)) =
      iB (k • FreeAbelianGroup.of γS) :=
    hv.trans (congrArg (fun v : B0 => iB v)
      (singularRegularPullbackCoefficientIso_inv_smul_of f y a γ k))
  let Z : ModuleCat.{u} ℤ := ModuleCat.of ℤ (ULift.{u} ℤ)
  let W : SSet.{u} := pullback sf (SSet.KanComplex.nativeCoverProjection SY ys)
  let e : SSet.localCoefficientChainComplex ((SSet.LocalSystem.pullback sf K)) ≅ W.chainComplex Z :=
    SSet.KanComplex.regularLocalCoefficientPullbackCoverChainIso sf ys
  have h0 := SSet.KanComplex.regularLocalCoefficientPullbackCoverChainIso_hom_ι_basis
    sf ys n s γS k
  change e.hom.f n (H (iA (k • FreeAbelianGroup.of γ))) = _
  exact (congrArg (fun v : B => e.hom.f n v) hc).trans h0

/-- The original topological chain map commutes with the literal pulled-back cover's snd. -/
theorem originalTopRegularCoverChainMap_square {X Y : TopCat.{u}}
    (f : X ⟶ Y) (y : Y) :
    TopCat.localCoefficientPullbackChainMap f
        (CategoryTheory.regularPathModuleCoefficientFunctor (_root_.FundamentalGroupoid.mk y)) ≫
      (originalTopRegularCoverChainIso Y y).hom =
        (originalTopRegularPullbackCoverChainIso f y).hom ≫
          SSet.chainComplexMap
            (pullback.snd (TopCat.toSSet.map f)
              (SSet.KanComplex.nativeCoverProjection (TopCat.toSSet.obj Y)
                (TopCat.toSSetObj₀Equiv.symm y))) (ModuleCat.of ℤ (ULift.{u} ℤ)) := by
  let sf := TopCat.toSSet.map f
  let SY := TopCat.toSSet.obj Y
  let ys : SY _⦋0⦌ := TopCat.toSSetObj₀Equiv.symm y
  let K : SSet.LocalSystem ℤ SY := CategoryTheory.regularPathModuleCoefficientFunctor
    (SSet.FundamentalGroupoid.mk ys)
  let L : TopCat.LocalSystem ℤ Y := CategoryTheory.regularPathModuleCoefficientFunctor
    (_root_.FundamentalGroupoid.mk y)
  let Z : ModuleCat.{u} ℤ := ModuleCat.of ℤ (ULift.{u} ℤ)
  let A : ChainComplex (ModuleCat.{u} ℤ) ℕ :=
    TopCat.localCoefficientChainComplex ((TopCat.LocalSystem.pullback f L))
  let B : ChainComplex (ModuleCat.{u} ℤ) ℕ := TopCat.localCoefficientChainComplex L
  let P : ChainComplex (ModuleCat.{u} ℤ) ℕ :=
    SSet.localCoefficientChainComplex ((SSet.LocalSystem.pullback sf K))
  let Q : ChainComplex (ModuleCat.{u} ℤ) ℕ := SSet.localCoefficientChainComplex K
  let W : ChainComplex (ModuleCat.{u} ℤ) ℕ :=
    (pullback sf (SSet.KanComplex.nativeCoverProjection SY ys)).chainComplex Z
  let V : ChainComplex (ModuleCat.{u} ℤ) ℕ := (SSet.KanComplex.nativeCover SY ys).chainComplex Z
  let M : A ⟶ B := TopCat.localCoefficientPullbackChainMap f L
  let N : P ⟶ Q := SSet.localCoefficientPullbackChainMap sf K
  let eS : P ≅ A := singularRegularPullbackCoefficientChainIso f y
  let eT : Q ≅ B := singularRegularCoefficientChainIso Y y
  let cS : P ≅ W := SSet.KanComplex.regularLocalCoefficientPullbackCoverChainIso sf ys
  let cT : Q ≅ V := SSet.KanComplex.originalNativeRegularCoefficientCoverChainIso SY ys
  let snd : W ⟶ V :=
    SSet.chainComplexMap (pullback.snd sf (SSet.KanComplex.nativeCoverProjection SY ys)) Z
  have hCoeff : M ≫ eT.inv = eS.inv ≫ N :=
    originalTopRegularCoefficientChainMap_square f y
  have hCover : N ≫ cT.hom = cS.hom ≫ snd :=
    SSet.KanComplex.originalRegularPullbackChainMap_cover_square sf ys
  change M ≫ (eT.inv ≫ cT.hom) = (eS.inv ≫ cS.hom) ≫ snd
  calc
    M ≫ (eT.inv ≫ cT.hom) = (M ≫ eT.inv) ≫ cT.hom :=
      (Category.assoc M eT.inv cT.hom).symm
    _ = (eS.inv ≫ N) ≫ cT.hom := congrArg (fun h : A ⟶ Q => h ≫ cT.hom) hCoeff
    _ = eS.inv ≫ (N ≫ cT.hom) := Category.assoc eS.inv N cT.hom
    _ = eS.inv ≫ (cS.hom ≫ snd) := congrArg (fun h : P ⟶ V => eS.inv ≫ h) hCover
    _ = (eS.inv ≫ cS.hom) ≫ snd := (Category.assoc eS.inv cS.hom snd).symm

/-- Actual original topological homology maps have the same literal cover naturality square. -/
theorem originalTopRegularCoverHomologyMap_square {X Y : TopCat.{u}}
    (f : X ⟶ Y) (y : Y) (n : ℕ) :
    HomologicalComplex.homologyMap
        (TopCat.localCoefficientPullbackChainMap f
          (CategoryTheory.regularPathModuleCoefficientFunctor
            (_root_.FundamentalGroupoid.mk y))) n ≫
      HomologicalComplex.homologyMap (originalTopRegularCoverChainIso Y y).hom n =
        HomologicalComplex.homologyMap (originalTopRegularPullbackCoverChainIso f y).hom n ≫
          HomologicalComplex.homologyMap
            (SSet.chainComplexMap
              (pullback.snd (TopCat.toSSet.map f)
                (SSet.KanComplex.nativeCoverProjection (TopCat.toSSet.obj Y)
                  (TopCat.toSSetObj₀Equiv.symm y))) (ModuleCat.of ℤ (ULift.{u} ℤ))) n := by
  let L : TopCat.LocalSystem ℤ Y := CategoryTheory.regularPathModuleCoefficientFunctor
    (_root_.FundamentalGroupoid.mk y)
  let Z : ModuleCat.{u} ℤ := ModuleCat.of ℤ (ULift.{u} ℤ)
  let A : ChainComplex (ModuleCat.{u} ℤ) ℕ :=
    TopCat.localCoefficientChainComplex ((TopCat.LocalSystem.pullback f L))
  let B : ChainComplex (ModuleCat.{u} ℤ) ℕ := TopCat.localCoefficientChainComplex L
  let P : ChainComplex (ModuleCat.{u} ℤ) ℕ :=
    (pullback (TopCat.toSSet.map f)
      (SSet.KanComplex.nativeCoverProjection (TopCat.toSSet.obj Y)
        (TopCat.toSSetObj₀Equiv.symm y))).chainComplex Z
  let Q : ChainComplex (ModuleCat.{u} ℤ) ℕ :=
    SSet.chainComplex
      (SSet.KanComplex.nativeCover (TopCat.toSSet.obj Y) (TopCat.toSSetObj₀Equiv.symm y)) Z
  let M : A ⟶ B := TopCat.localCoefficientPullbackChainMap f L
  let eS : A ≅ P := originalTopRegularPullbackCoverChainIso f y
  let eT : B ≅ Q := originalTopRegularCoverChainIso Y y
  let snd : P ⟶ Q := SSet.chainComplexMap
    (pullback.snd (TopCat.toSSet.map f)
      (SSet.KanComplex.nativeCoverProjection (TopCat.toSSet.obj Y)
        (TopCat.toSSetObj₀Equiv.symm y))) Z
  have hs : M ≫ eT.hom = eS.hom ≫ snd := originalTopRegularCoverChainMap_square f y
  have h := congrArg (fun h : A ⟶ Q => HomologicalComplex.homologyMap h n) hs
  change HomologicalComplex.homologyMap M n ≫ HomologicalComplex.homologyMap eT.hom n =
    HomologicalComplex.homologyMap eS.hom n ≫ HomologicalComplex.homologyMap snd n
  simpa only [HomologicalComplex.homologyMap_comp] using h

end TopCat

namespace TopCat

/-- Ordinary inverse loop labels index the actual topological coefficient arrows at y. -/
noncomputable def regularBasedGroupRingIndexEquiv (Y : TopCat.{u}) (y : Y) :
    (_root_.FundamentalGroupoid.mk y ⟶ _root_.FundamentalGroupoid.mk y) ≃
      _root_.FundamentalGroup Y y :=
  { toFun := fun γ => (_root_.FundamentalGroup.fromArrow γ)⁻¹
    invFun := fun a => _root_.FundamentalGroup.toArrow (a⁻¹)
    left_inv := by
      intro γ
      change (((End.of γ)⁻¹)⁻¹).asHom = γ
      rw [inv_inv]
    right_inv := by
      intro a
      change (a⁻¹)⁻¹ = a
      exact inv_inv a }

/-- The actual topological regular coefficient at y is its literal integral group ring. -/
noncomputable def regularBasedGroupRingIso (Y : TopCat.{u}) (y : Y) :
    (CategoryTheory.regularPathModuleCoefficientFunctor (_root_.FundamentalGroupoid.mk y)).obj
        (_root_.FundamentalGroupoid.mk y) ≅
      ModuleCat.of ℤ (MonoidAlgebra ℤ (_root_.FundamentalGroup Y y)) := by
  let b := _root_.FundamentalGroupoid.mk y
  let H : Type u := b ⟶ b
  let G : Type u := _root_.FundamentalGroup Y y
  let e : FreeAbelianGroup H ≃+ (H →₀ ℤ) := FreeAbelianGroup.equivFinsupp H
  let q : FreeAbelianGroup H ≃ₗ[ℤ] (H →₀ ℤ) :=
    e.toLinearEquiv (fun z t => (e.toAddMonoidHom.toIntLinearMap).map_smul z t)
  let d : (H →₀ ℤ) ≃ₗ[ℤ] (G →₀ ℤ) :=
    Finsupp.domLCongr (regularBasedGroupRingIndexEquiv Y y)
  let c : MonoidAlgebra ℤ G ≃ₗ[ℤ] (G →₀ ℤ) := MonoidAlgebra.coeffLinearEquiv ℤ
  change ModuleCat.of ℤ (FreeAbelianGroup H) ≅ ModuleCat.of ℤ (MonoidAlgebra ℤ G)
  exact ((q.trans d).trans c.symm).toModuleIso

/-- Every original topological coefficient path and integer keep their ordinary inverse label. -/
theorem regularBasedGroupRingIso_hom_zsmul (Y : TopCat.{u}) (y : Y)
    (γ : _root_.FundamentalGroupoid.mk y ⟶ _root_.FundamentalGroupoid.mk y) (z : ℤ) :
    (regularBasedGroupRingIso Y y).hom (z • FreeAbelianGroup.of γ) =
      MonoidAlgebra.single (_root_.FundamentalGroup.fromArrow γ)⁻¹ z := by
  let b := _root_.FundamentalGroupoid.mk y
  let A : ModuleCat.{u} ℤ := (CategoryTheory.regularPathModuleCoefficientFunctor b).obj b
  let G : Type u := _root_.FundamentalGroup Y y
  let R : Type u := MonoidAlgebra ℤ G
  let e := regularBasedGroupRingIso Y y
  let j : G := regularBasedGroupRingIndexEquiv Y y γ
  have h0 : e.hom (FreeAbelianGroup.of γ : A) = MonoidAlgebra.single j (1 : ℤ) := by
    change MonoidAlgebra.ofCoeff
        ((Finsupp.domLCongr (regularBasedGroupRingIndexEquiv Y y) :
          ((b ⟶ b) →₀ ℤ) ≃ₗ[ℤ] (G →₀ ℤ))
          (FreeAbelianGroup.toFinsupp (FreeAbelianGroup.of γ))) =
      MonoidAlgebra.single j (1 : ℤ)
    rw [FreeAbelianGroup.toFinsupp_of, Finsupp.domLCongr_single]
    rfl
  have hs : z • (MonoidAlgebra.single j (1 : ℤ) : R) = MonoidAlgebra.single j z :=
    (MonoidAlgebra.smul_single' z j (1 : ℤ)).trans
      (congrArg (MonoidAlgebra.single j) (mul_one z))
  change e.hom (z • (FreeAbelianGroup.of γ : A)) = MonoidAlgebra.single j z
  exact (e.hom.hom.map_smul z (FreeAbelianGroup.of γ : A)).trans
    ((congrArg (fun t : R => z • t) h0).trans hs)

/-- A literal topological group-ring basis element returns its original inverse loop path. -/
theorem regularBasedGroupRingIso_inv_single (Y : TopCat.{u}) (y : Y)
    (a : _root_.FundamentalGroup Y y) (z : ℤ) :
    (regularBasedGroupRingIso Y y).inv (MonoidAlgebra.single a z) =
      z • FreeAbelianGroup.of (_root_.FundamentalGroup.toArrow (a⁻¹)) := by
  let b := _root_.FundamentalGroupoid.mk y
  let A : ModuleCat.{u} ℤ := (CategoryTheory.regularPathModuleCoefficientFunctor b).obj b
  let B : ModuleCat.{u} ℤ := ModuleCat.of ℤ
    (MonoidAlgebra ℤ (_root_.FundamentalGroup Y y))
  let e := regularBasedGroupRingIso Y y
  let γ : b ⟶ b := _root_.FundamentalGroup.toArrow (a⁻¹)
  have hj : (_root_.FundamentalGroup.fromArrow γ)⁻¹ = a :=
    (regularBasedGroupRingIndexEquiv Y y).apply_symm_apply a
  have hf : e.hom (z • (FreeAbelianGroup.of γ : A)) = MonoidAlgebra.single a z :=
    (regularBasedGroupRingIso_hom_zsmul Y y γ z).trans
      (congrArg (fun g : _root_.FundamentalGroup Y y => MonoidAlgebra.single g z) hj)
  have hi : e.inv (e.hom (z • (FreeAbelianGroup.of γ : A))) =
      z • (FreeAbelianGroup.of γ : A) :=
    congrArg (fun h : A ⟶ A => h (z • (FreeAbelianGroup.of γ : A))) e.hom_inv_id
  exact (congrArg (fun t : B => e.inv t) hf.symm).trans hi

/-- The actual topological regular coefficient has the ordinary integral group-ring basis. -/
noncomputable def regularBasedGroupRingBasis (Y : TopCat.{u}) (y : Y) :
    Module.Basis (_root_.FundamentalGroup Y y) ℤ
      ((CategoryTheory.regularPathModuleCoefficientFunctor (_root_.FundamentalGroupoid.mk y)).obj
        (_root_.FundamentalGroupoid.mk y)) :=
  (MonoidAlgebra.basis (_root_.FundamentalGroup Y y) ℤ).map
    (regularBasedGroupRingIso Y y).toLinearEquiv.symm

/-- Its basis vector at a is the actual coefficient path represented by the inverse loop a⁻¹. -/
theorem regularBasedGroupRingBasis_apply (Y : TopCat.{u}) (y : Y)
    (a : _root_.FundamentalGroup Y y) :
    regularBasedGroupRingBasis Y y a =
      FreeAbelianGroup.of (_root_.FundamentalGroup.toArrow (a⁻¹)) := by
  let b := _root_.FundamentalGroupoid.mk y
  let A : ModuleCat.{u} ℤ := (CategoryTheory.regularPathModuleCoefficientFunctor b).obj b
  let e := regularBasedGroupRingIso Y y
  let γ : b ⟶ b := _root_.FundamentalGroup.toArrow (a⁻¹)
  have h : e.inv (MonoidAlgebra.single a (1 : ℤ)) = (1 : ℤ) • (FreeAbelianGroup.of γ : A) :=
    regularBasedGroupRingIso_inv_single Y y a (1 : ℤ)
  change e.inv (MonoidAlgebra.single a (1 : ℤ)) = (FreeAbelianGroup.of γ : A)
  exact h.trans (one_smul ℤ (FreeAbelianGroup.of γ : A))

/-- Original positive loop transport is right multiplication by its inverse group-ring label. -/
theorem regularBasedGroupRingIso_postcomp_positive (Y : TopCat.{u}) (y : Y)
    (a : _root_.FundamentalGroup Y y)
    (t : (CategoryTheory.regularPathModuleCoefficientFunctor (_root_.FundamentalGroupoid.mk y)).obj
      (_root_.FundamentalGroupoid.mk y)) :
    (regularBasedGroupRingIso Y y).hom
        ((CategoryTheory.regularPathModuleCoefficientFunctor (_root_.FundamentalGroupoid.mk y)).map
          (_root_.FundamentalGroup.toArrow a) t) =
      (regularBasedGroupRingIso Y y).hom t * MonoidAlgebra.single a⁻¹ (1 : ℤ) := by
  let b := _root_.FundamentalGroupoid.mk y
  let A : ModuleCat.{u} ℤ := (CategoryTheory.regularPathModuleCoefficientFunctor b).obj b
  let R : Type u := MonoidAlgebra ℤ (_root_.FundamentalGroup Y y)
  let e := regularBasedGroupRingIso Y y
  let J := regularBasedGroupRingIndexEquiv Y y
  let T : A ⟶ A := (CategoryTheory.regularPathModuleCoefficientFunctor b).map
    (_root_.FundamentalGroup.toArrow a)
  let fL : A →+ R := e.hom.hom.toAddMonoidHom.comp T.hom.toAddMonoidHom
  let fR : A →+ R := (AddMonoidHom.mulRight (MonoidAlgebra.single a⁻¹ (1 : ℤ))).comp
    e.hom.hom.toAddMonoidHom
  have hpoint : ∀ γ : b ⟶ b,
      e.hom (FreeAbelianGroup.of γ : A) = MonoidAlgebra.single (J γ) (1 : ℤ) := by
    intro γ
    exact (congrArg (fun v : A => e.hom v)
      (one_smul ℤ (FreeAbelianGroup.of γ : A)).symm).trans
        (regularBasedGroupRingIso_hom_zsmul Y y γ (1 : ℤ))
  have hmaps : fL = fR := by
    refine FreeAbelianGroup.lift_ext _ _ ?_
    intro γ
    let γ' : b ⟶ b := γ ≫ _root_.FundamentalGroup.toArrow a
    have hT : T (FreeAbelianGroup.of γ : A) = (FreeAbelianGroup.of γ' : A) :=
      CategoryTheory.regularPathModuleCoefficientFunctor_map_of b
        (_root_.FundamentalGroup.toArrow a) γ
    have hEnd : End.of γ' = a * End.of γ := rfl
    have hJ : J γ' = J γ * a⁻¹ := by
      change (End.of γ')⁻¹ = (End.of γ)⁻¹ * a⁻¹
      rw [hEnd, mul_inv_rev]
    have hl : e.hom (T (FreeAbelianGroup.of γ : A)) =
        MonoidAlgebra.single (J γ') (1 : ℤ) :=
      (congrArg (fun v : A => e.hom v) hT).trans (hpoint γ')
    have hprod : (MonoidAlgebra.single (J γ) (1 : ℤ) : R) *
          MonoidAlgebra.single a⁻¹ (1 : ℤ) =
        MonoidAlgebra.single (J γ * a⁻¹) (1 : ℤ) := by
      simpa only [one_mul] using
        (MonoidAlgebra.single_mul_single (J γ) a⁻¹ (1 : ℤ) (1 : ℤ))
    have hr : e.hom (FreeAbelianGroup.of γ : A) * MonoidAlgebra.single a⁻¹ (1 : ℤ) =
        MonoidAlgebra.single (J γ * a⁻¹) (1 : ℤ) :=
      (congrArg (fun v : R => v * MonoidAlgebra.single a⁻¹ (1 : ℤ)) (hpoint γ)).trans hprod
    change e.hom (T (FreeAbelianGroup.of γ : A)) =
      e.hom (FreeAbelianGroup.of γ : A) * MonoidAlgebra.single a⁻¹ (1 : ℤ)
    exact (hl.trans (congrArg
      (fun g : _root_.FundamentalGroup Y y => MonoidAlgebra.single g (1 : ℤ)) hJ)).trans hr.symm
  exact congrArg (fun h : A →+ R => h t) hmaps

/-- Inverse loop transport is right multiplication by the positive ordinary group-ring label. -/
theorem regularBasedGroupRingIso_postcomp_inverse (Y : TopCat.{u}) (y : Y)
    (a : _root_.FundamentalGroup Y y)
    (t : (CategoryTheory.regularPathModuleCoefficientFunctor (_root_.FundamentalGroupoid.mk y)).obj
      (_root_.FundamentalGroupoid.mk y)) :
    (regularBasedGroupRingIso Y y).hom
        ((CategoryTheory.regularPathModuleCoefficientFunctor (_root_.FundamentalGroupoid.mk y)).map
          (_root_.FundamentalGroup.toArrow (a⁻¹)) t) =
      (regularBasedGroupRingIso Y y).hom t * MonoidAlgebra.single a (1 : ℤ) := by
  have h := regularBasedGroupRingIso_postcomp_positive Y y a⁻¹ t
  simpa only [inv_inv] using h

end TopCat
