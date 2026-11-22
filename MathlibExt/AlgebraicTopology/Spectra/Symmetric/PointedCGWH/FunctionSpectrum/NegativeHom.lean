/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.Delooping
import MathlibExt.CategoryTheory.Functor.Iteration
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenOrdinaryHoHom
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.ScalarCompatibility
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.ScalarSphereSuspensionComparison
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.LevelFibrancy
import Mathlib.CategoryTheory.HomCongr

/-!
# Negative Hom equivalences for symmetric Ω-spectra

In the native projective homotopy category, the Hom from the cone suspension of QX to the
first delooping of an Ω-spectrum E is naturally equivalent to the Hom from X to E. The
construction uses the specified cofibrant-replacement counit, the comparison with sphere
suspension and the suspension-loop adjunction. Both directions are natural in source and
target maps, and iterated delooping preserves the Ω condition.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed CGWH.modelCategory

namespace NativeOmegaRecovery.NativeSymmetricDelooping

private abbrev V := PointedCGWH.{u, v}
private abbrev J := PointedCGWH.SymmetricOperatorIndex.{u, v}
private abbrev Carrier := EnrichedFunctorCat V.{u, v} J.{u, v}
open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
attribute [local instance] modelCategory

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

private abbrev Q := Replacement.cofibrantReplacement (B := B) (A := J.{u, v})
private abbrev H := toHomotopyCategory Carrier.{u, v}
private abbrev ISusp := OriginalISuspension.suspension (B := B) (I := J.{u, v})
private abbrev ScalarSusp := EnrichedFunctorCat.tensorLeft
    (A := J.{u, v}) PointedCGWH.sphereOne.{u, v}
private abbrev ScalarLoop := cotensor (I := J.{u, v}) PointedCGWH.sphereOne.{u, v}
private abbrev scalarAdjunction := ScalarLeibniz.adjunction (A := J.{u, v})
  PointedCGWH.sphereOne.{u, v}

/-- The endpoint iso is constructed by inverting the actual level-weak original delta. -/
def deltaHoIso (E : Carrier.{u, v}) (hE : Actual.SymmetricIsOmega E) :
    H.{u, v}.obj E ≅ H.{u, v}.obj (ScalarLoop.obj (firstDelooping.obj E)) := by
  exact @asIso _ _ _ _ (H.{u, v}.map (delta.app E))
    (Localization.inverts H.{u, v} (weakEquivalences Carrier.{u, v})
      (delta.app E) (delta_weak E hE))

/-- Its forward map is exactly the original delta in the actual level homotopy category. -/
theorem deltaHoIso_hom (E : Carrier.{u, v}) (hE : Actual.SymmetricIsOmega E) :
    (deltaHoIso E hE).hom = H.{u, v}.map (delta.app E) := rfl

/-- The original same-cardinal Q counit is used as the source endpoint iso. -/
def epsilonHoIso (X : Carrier.{u, v}) : H.{u, v}.obj (Q.obj X) ≅ H.{u, v}.obj X :=
  (Replacement.cofibrantReplacementProjectionIso (B := B) (A := J.{u, v})).app X

/-- The source endpoint is the entire original Q counit. -/
theorem epsilonHoIso_hom (X : Carrier.{u, v}) :
    (epsilonHoIso (B := B) X).hom =
      H.{u, v}.map ((Replacement.cofibrantReplacementCounit (B := B)).app X) := rfl

/-- The original I-cone/scalar-sphere comparison supplies the suspension endpoint. -/
def suspensionHoIso (X : Carrier.{u, v}) :
    H.{u, v}.obj (ISusp.obj (Q.obj X)) ≅ H.{u, v}.obj (ScalarSusp.obj (Q.obj X)) :=
  (ScalarSphereSuspension.originalISuspensionQIsoSphereQ (B := B) (I := J.{u, v})).app X

/-- The actual scalar Quillen adjunction provides the whole Hom equivalence on original Q. -/
def scalarHomEquiv (X E : Carrier.{u, v}) :
    (H.{u, v}.obj (ScalarSusp.obj (Q.obj X)) ⟶ H.{u, v}.obj (firstDelooping.obj E)) ≃
      (H.{u, v}.obj (Q.obj X) ⟶ H.{u, v}.obj (ScalarLoop.obj (firstDelooping.obj E))) := by
  letI : IsCofibrant PointedCGWH.sphereOne.{u, v} := PointedCGWH.modelCategory.sphereOne_isCofibrant
  letI : scalarAdjunction.{u, v}.IsQuillenAdjunction :=
    ScalarCompatibility.scalar_isQuillen (B := B) PointedCGWH.sphereOne.{u, v}
  letI : IsCofibrant (Q.obj X) := Replacement.isCofibrant_cofibrantReplacement (B := B) X
  letI : IsFibrant (firstDelooping.obj E) := allObjectsFibrant (B := B) _
  exact QuillenOrdinaryHoHom.homEquiv scalarAdjunction (Q.obj X) (firstDelooping.obj E)

/-- The full negative-degree Hom identification uses the original I suspension,
Q counit, actual scalar adjunct and genuine first-free-S0 delta. -/
def negativeHomEquiv (X E : Carrier.{u, v}) (hE : Actual.SymmetricIsOmega E) :
    (H.{u, v}.obj (ISusp.obj (Q.obj X)) ⟶ H.{u, v}.obj (firstDelooping.obj E)) ≃
      (H.{u, v}.obj X ⟶ H.{u, v}.obj E) :=
  (Iso.homCongr (suspensionHoIso (B := B) X) (Iso.refl _)).trans
    ((scalarHomEquiv (B := B) X E).trans
      (Iso.homCongr (epsilonHoIso (B := B) X) (deltaHoIso E hE).symm))

/-- Every full forward function retains the source's exact three original endpoint maps. -/
theorem negativeHomEquiv_apply (X E : Carrier.{u, v}) (hE : Actual.SymmetricIsOmega E)
    (g : H.{u, v}.obj (ISusp.obj (Q.obj X)) ⟶ H.{u, v}.obj (firstDelooping.obj E)) :
    negativeHomEquiv (B := B) X E hE g =
      (epsilonHoIso (B := B) X).inv ≫
        scalarHomEquiv (B := B) X E ((suspensionHoIso (B := B) X).inv ≫ g) ≫
        (deltaHoIso E hE).inv := by
  simp only [negativeHomEquiv, Equiv.trans_apply, Iso.homCongr_apply,
    Iso.refl_hom, Category.comp_id, Iso.symm_hom]

/-- The full inverse function retains the same original maps and inverse scalar adjunct. -/
theorem negativeHomEquiv_symm_apply (X E : Carrier.{u, v}) (hE : Actual.SymmetricIsOmega E)
    (h : H.{u, v}.obj X ⟶ H.{u, v}.obj E) :
    (negativeHomEquiv (B := B) X E hE).symm h =
      (suspensionHoIso (B := B) X).hom ≫
        (scalarHomEquiv (B := B) X E).symm
          ((epsilonHoIso (B := B) X).hom ≫ h ≫ (deltaHoIso E hE).hom) := by
  simp only [negativeHomEquiv, Equiv.symm_trans_apply, Iso.homCongr_symm,
    Iso.homCongr_apply, Iso.refl_inv, Category.comp_id, Iso.symm_hom, Iso.symm_inv]

private theorem scalarQuillen : scalarAdjunction.{u, v}.IsQuillenAdjunction := by
  let : IsCofibrant PointedCGWH.sphereOne.{u, v} := PointedCGWH.modelCategory.sphereOne_isCofibrant
  exact ScalarCompatibility.scalar_isQuillen (B := B) PointedCGWH.sphereOne.{u, v}
attribute [local instance] scalarQuillen

private theorem cofibrantQ (X : Carrier.{u, v}) : IsCofibrant (Q.obj X) :=
  Replacement.isCofibrant_cofibrantReplacement (B := B) X
attribute [local instance] cofibrantQ

private theorem fibrantDelooping (E : Carrier.{u, v}) : IsFibrant (firstDelooping.obj E) :=
  allObjectsFibrant (B := B) _
attribute [local instance] fibrantDelooping

/-- The scalar Hom equivalence retains each original Q source transformation. -/
theorem scalarHomEquiv_naturality_left {X X' : Carrier.{u, v}} (f : X' ⟶ X)
    (E : Carrier.{u, v})
    (g : H.{u, v}.obj (ScalarSusp.obj (Q.obj X)) ⟶ H.{u, v}.obj (firstDelooping.obj E)) :
    scalarHomEquiv (B := B) X' E (H.{u, v}.map (ScalarSusp.map (Q.map f)) ≫ g) =
      H.{u, v}.map (Q.map f) ≫ scalarHomEquiv (B := B) X E g :=
  QuillenOrdinaryHoHom.homEquiv_naturality_left scalarAdjunction (firstDelooping.obj E) (Q.map f) g

/-- The same full Hom function retains every original function-delooping target map. -/
theorem scalarHomEquiv_naturality_right (X : Carrier.{u, v})
    {E E' : Carrier.{u, v}} (t : E ⟶ E')
    (g : H.{u, v}.obj (ScalarSusp.obj (Q.obj X)) ⟶ H.{u, v}.obj (firstDelooping.obj E)) :
    scalarHomEquiv (B := B) X E' (g ≫ H.{u, v}.map (firstDelooping.map t)) =
      scalarHomEquiv (B := B) X E g ≫ H.{u, v}.map (ScalarLoop.map (firstDelooping.map t)) :=
  QuillenOrdinaryHoHom.homEquiv_naturality_right scalarAdjunction (Q.obj X) g (firstDelooping.map t)

omit B in
private theorem inverse_square {C : Type*} [Category C]
    {X X' Y Y' : C} (e : X ≅ Y) (e' : X' ≅ Y') (f : X ⟶ X') (g : Y ⟶ Y')
    (h : f ≫ e'.hom = e.hom ≫ g) : g ≫ e'.inv = e.inv ≫ f := by
  apply (cancel_epi e.hom).1
  have h' := congrArg (fun z => z ≫ e'.inv) h
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id] using h'.symm

/-- The inverse of the actual weak delta keeps its entire original target naturality. -/
theorem deltaHoIso_inv_naturality {E E' : Carrier.{u, v}}
    (hE : Actual.SymmetricIsOmega E) (hE' : Actual.SymmetricIsOmega E') (t : E ⟶ E') :
    H.{u, v}.map (ScalarLoop.map (firstDelooping.map t)) ≫ (deltaHoIso E' hE').inv =
      (deltaHoIso E hE).inv ≫ H.{u, v}.map t := by
  apply inverse_square (deltaHoIso E hE) (deltaHoIso E' hE')
  rw [deltaHoIso_hom, deltaHoIso_hom]
  change H.{u, v}.map t ≫ H.{u, v}.map (delta.app E') =
    H.{u, v}.map (delta.app E) ≫ H.{u, v}.map (firstDeloopingLoop.map t)
  exact (H.{u, v}.map_comp t (delta.app E')).symm.trans
    ((congrArg (fun q => H.{u, v}.map q) (delta_naturality t)).trans
      (H.{u, v}.map_comp (delta.app E) (firstDeloopingLoop.map t)))

/-- Every inverse Q endpoint retains the same original full Q naturality. -/
theorem epsilonHoIso_inv_naturality {X X' : Carrier.{u, v}} (f : X' ⟶ X) :
    H.{u, v}.map f ≫ (epsilonHoIso (B := B) X).inv =
      (epsilonHoIso (B := B) X').inv ≫ H.{u, v}.map (Q.map f) :=
  (Replacement.cofibrantReplacementProjectionIso (B := B) (A := J.{u, v})).inv.naturality f

/-- The inverse suspension endpoint retains both original same-Q source maps. -/
theorem suspensionHoIso_inv_naturality {X X' : Carrier.{u, v}} (f : X' ⟶ X) :
    H.{u, v}.map (ScalarSusp.map (Q.map f)) ≫ (suspensionHoIso (B := B) X).inv =
      (suspensionHoIso (B := B) X').inv ≫ H.{u, v}.map (ISusp.map (Q.map f)) :=
  (ScalarSphereSuspension.originalISuspensionQIsoSphereQ (B := B) (I := J.{u, v})).inv.naturality f

/-- The negative Hom identification is natural on every whole original source arrow. -/
theorem negativeHomEquiv_naturality_left {X X' : Carrier.{u, v}} (f : X' ⟶ X)
    (E : Carrier.{u, v}) (hE : Actual.SymmetricIsOmega E)
    (g : H.{u, v}.obj (ISusp.obj (Q.obj X)) ⟶ H.{u, v}.obj (firstDelooping.obj E)) :
    negativeHomEquiv (B := B) X' E hE (H.{u, v}.map (ISusp.map (Q.map f)) ≫ g) =
      H.{u, v}.map f ≫ negativeHomEquiv (B := B) X E hE g := by
  rw [negativeHomEquiv_apply, negativeHomEquiv_apply]
  have ha := suspensionHoIso_inv_naturality (B := B) f
  have he := epsilonHoIso_inv_naturality (B := B) f
  have hg : (suspensionHoIso (B := B) X').inv ≫
      (H.{u, v}.map (ISusp.map (Q.map f)) ≫ g) =
    H.{u, v}.map (ScalarSusp.map (Q.map f)) ≫ ((suspensionHoIso (B := B) X).inv ≫ g) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ g) ha.symm).trans (Category.assoc _ _ _))
  rw [hg, scalarHomEquiv_naturality_left]
  simpa only [Category.assoc] using congrArg
    (fun z => z ≫ scalarHomEquiv (B := B) X E ((suspensionHoIso (B := B) X).inv ≫ g) ≫
      (deltaHoIso E hE).inv) he.symm

/-- Every Omega target map retains the whole original function-delooping action. -/
theorem negativeHomEquiv_naturality_right (X : Carrier.{u, v})
    {E E' : Carrier.{u, v}} (hE : Actual.SymmetricIsOmega E) (hE' : Actual.SymmetricIsOmega E')
    (t : E ⟶ E')
    (g : H.{u, v}.obj (ISusp.obj (Q.obj X)) ⟶ H.{u, v}.obj (firstDelooping.obj E)) :
    negativeHomEquiv (B := B) X E' hE' (g ≫ H.{u, v}.map (firstDelooping.map t)) =
      negativeHomEquiv (B := B) X E hE g ≫ H.{u, v}.map t := by
  rw [negativeHomEquiv_apply, negativeHomEquiv_apply]
  rw [← Category.assoc (suspensionHoIso (B := B) X).inv g,
    scalarHomEquiv_naturality_right]
  have hd := deltaHoIso_inv_naturality hE hE' t
  simpa only [Category.assoc] using congrArg
    (fun z => (epsilonHoIso (B := B) X).inv ≫
      scalarHomEquiv (B := B) X E ((suspensionHoIso (B := B) X).inv ≫ g) ≫ z) hd

/-- The inverse negative function keeps all original source naturalities too. -/
theorem negativeHomEquiv_symm_naturality_left {X X' : Carrier.{u, v}} (f : X' ⟶ X)
    (E : Carrier.{u, v}) (hE : Actual.SymmetricIsOmega E) (h : H.{u, v}.obj X ⟶ H.{u, v}.obj E) :
    (negativeHomEquiv (B := B) X' E hE).symm (H.{u, v}.map f ≫ h) =
      H.{u, v}.map (ISusp.map (Q.map f)) ≫ (negativeHomEquiv (B := B) X E hE).symm h := by
  apply (negativeHomEquiv (B := B) X' E hE).injective
  rw [Equiv.apply_symm_apply, negativeHomEquiv_naturality_left, Equiv.apply_symm_apply]

/-- The same actual inverse retains every complete Omega target transformation. -/
theorem negativeHomEquiv_symm_naturality_right (X : Carrier.{u, v})
    {E E' : Carrier.{u, v}} (hE : Actual.SymmetricIsOmega E) (hE' : Actual.SymmetricIsOmega E')
    (t : E ⟶ E') (h : H.{u, v}.obj X ⟶ H.{u, v}.obj E) :
    (negativeHomEquiv (B := B) X E' hE').symm (h ≫ H.{u, v}.map t) =
      (negativeHomEquiv (B := B) X E hE).symm h ≫ H.{u, v}.map (firstDelooping.map t) := by
  apply (negativeHomEquiv (B := B) X E' hE').injective
  rw [Equiv.apply_symm_apply, negativeHomEquiv_naturality_right X hE hE' t, Equiv.apply_symm_apply]

/-- Every negative iteration uses the same whole first-free-S0 function-spectrum functor. -/
def iteratedDelooping (n : ℕ) : Carrier.{u, v} ⥤ Carrier.{u, v} :=
  Functor.Iteration.iterate firstDelooping n

omit B in
/-- The entire successor functor retains the original preceding iteration and first function
spectrum. -/
theorem iteratedDelooping_succ (n : ℕ) :
    iteratedDelooping.{u, v} (n + 1) = iteratedDelooping n ⋙ firstDelooping := rfl

omit B in
/-- Every negative iteration preserves the full original all-label Omega predicate. -/
theorem iteratedDelooping_isOmega (n : ℕ) (E : Carrier.{u, v}) (hE : Actual.SymmetricIsOmega E) :
    Actual.SymmetricIsOmega ((iteratedDelooping n).obj E) :=
  Functor.Iteration.preserves firstDelooping Actual.SymmetricIsOmega
    firstDelooping_isOmega n E hE

/-- Every successive negative target degree has the same genuine original suspension Hom
equivalence. -/
def negativeHomEquivIterate (n : ℕ) (X E : Carrier.{u, v}) (hE : Actual.SymmetricIsOmega E) :=
  negativeHomEquiv (B := B) X ((iteratedDelooping n).obj E) (iteratedDelooping_isOmega n E hE)

/-- Each complete negative-degree function retains the original same-Q source naturality. -/
theorem negativeHomEquiv_iterate_naturality_left (n : ℕ)
    {X X' : Carrier.{u, v}} (f : X' ⟶ X) (E : Carrier.{u, v}) (hE : Actual.SymmetricIsOmega E)
    (g : H.{u, v}.obj (ISusp.obj (Q.obj X)) ⟶
      H.{u, v}.obj (firstDelooping.obj ((iteratedDelooping n).obj E))) :
    negativeHomEquiv (B := B) X' ((iteratedDelooping n).obj E)
        (iteratedDelooping_isOmega n E hE) (H.{u, v}.map (ISusp.map (Q.map f)) ≫ g) =
      H.{u, v}.map f ≫ negativeHomEquiv (B := B) X ((iteratedDelooping n).obj E)
        (iteratedDelooping_isOmega n E hE) g :=
  negativeHomEquiv_naturality_left (B := B) f ((iteratedDelooping n).obj E)
    (iteratedDelooping_isOmega n E hE) g

/-- All negative degrees retain every original full Omega target transformation. -/
theorem negativeHomEquiv_iterate_naturality_right (n : ℕ) (X : Carrier.{u, v})
    {E E' : Carrier.{u, v}} (hE : Actual.SymmetricIsOmega E) (hE' : Actual.SymmetricIsOmega E')
    (t : E ⟶ E')
    (g : H.{u, v}.obj (ISusp.obj (Q.obj X)) ⟶
      H.{u, v}.obj (firstDelooping.obj ((iteratedDelooping n).obj E))) :
    negativeHomEquiv (B := B) X ((iteratedDelooping n).obj E')
        (iteratedDelooping_isOmega n E' hE')
        (g ≫ H.{u, v}.map (firstDelooping.map ((iteratedDelooping n).map t))) =
      negativeHomEquiv (B := B) X ((iteratedDelooping n).obj E)
        (iteratedDelooping_isOmega n E hE) g ≫ H.{u, v}.map ((iteratedDelooping n).map t) :=
  negativeHomEquiv_naturality_right (B := B) X (iteratedDelooping_isOmega n E hE)
    (iteratedDelooping_isOmega n E' hE') ((iteratedDelooping n).map t) g

end NativeOmegaRecovery.NativeSymmetricDelooping
