/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



module

public import MathlibExt.Algebra.Category.ModuleCat.BalancedTensor.CommutativeRightExact
public import MathlibExt.Algebra.Category.ModuleCat.FlatTensorAcyclic
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Logic.Small.Defs

/-!
# Flat induced targets are acyclic for balanced tensor functors

For a commutative acting ring, the opposite-ring action on the coefficient
module gives its corresponding left action. The balanced tensor functor is
naturally isomorphic to ordinary tensor followed by exact restriction of
scalars. A projective resolution of a flat target therefore computes zero
positive derived objects.

Extension of scalars takes a flat ground module to a flat acting-ring
module. Thus these induced targets are acyclic for the balanced functor.
The coefficient and ring carriers may lie in independent universes; the
coefficient module requires no flatness or projectivity assumption.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings
open MulOpposite

universe u v w z

namespace ModuleCat.BalancedTensor.InducedFlatAcyclic

variable (k : Type u) (R : Type v) [CommRing k] [CommRing R] [Algebra k R]
  (M : Type w) [AddCommGroup M] [Module k M] [Module Rᵐᵒᵖ M]
  [SMulCommClass k Rᵐᵒᵖ M] [IsScalarTower k Rᵐᵒᵖ M]

/-- The original right action supplies its commutative left form through the native opposite equivalence. -/
local instance (priority := 10) originalLeftModule : Module R M :=
  Module.compHom M (RingEquiv.toOpposite R).toRingHom

/-- The original ground action commutes with the left form of the original opposite action. -/
local instance originalLeftGroundComm : SMulCommClass k R M where
  smul_comm a r m := by
    change a • (op r • m) = op r • (a • m)
    exact smul_comm a (op r) m

/-- The original opposite scalar tower gives the same actual left scalar tower. -/
local instance originalLeftGroundTower : IsScalarTower k R M :=
  IsScalarTower.of_algebraMap_smul (fun a m => by
    change op (algebraMap k R a) • m = a • m
    simpa only [MulOpposite.algebraMap_apply] using
      (IsScalarTower.algebraMap_smul Rᵐᵒᵖ a m))

/-- Symmetry of the earned original ground commutation supplies the outer action. -/
local instance originalLeftGroundCommSymm : SMulCommClass R k M := SMulCommClass.symm k R M

attribute [local instance] ModuleCat.BalancedTensor.additive

/-- An actual flat acting-ring target is acyclic for the original right-coefficient balanced functor. -/
theorem isZero_leftDerived_flat_target (X : ModuleCat.{max u v z} R)
    [Module.Flat R X] (n : ℕ) :
    letI : Small.{max u v z} R := Small.mk'
      ((Equiv.ulift : ULift.{max u z} R ≃ R).symm)
    letI : EnoughProjectives (ModuleCat.{max u v z} R) :=
      @ModuleCat.enoughProjectives.{max u v z, v} R _ inferInstance
    letI : HasProjectiveResolutions (ModuleCat.{max u v z} R) :=
      ⟨fun _ => inferInstance⟩
    IsZero (((ModuleCat.BalancedTensor.functor k R M :
      ModuleCat.{max u v z} R ⥤ ModuleCat.{max u v w z} k).leftDerived (n + 1)).obj X) := by
  let : Small.{max u v z} R := Small.mk'
    ((Equiv.ulift : ULift.{max u z} R ≃ R).symm)
  let : EnoughProjectives (ModuleCat.{max u v z} R) :=
    @ModuleCat.enoughProjectives.{max u v z, v} R _ inferInstance
  let : HasProjectiveResolutions (ModuleCat.{max u v z} R) :=
    ⟨fun _ => inferInstance⟩
  let F : ModuleCat.{max u v z} R ⥤ ModuleCat.{max u v w z} k :=
    ModuleCat.BalancedTensor.functor k R M
  let : SMulCommClass k R M := originalLeftGroundComm (k := k) (R := R) (M := M)
  let : IsScalarTower k R M := originalLeftGroundTower (k := k) (R := R) (M := M)
  let hOp : ∀ (r : R) (m : M), op r • m = r • m := fun _ _ => rfl
  let := ModuleCat.BalancedTensor.actingOppositeComm (R := R) (M := M) hOp
  let L : ModuleCat.{max u v z} R ⥤ ModuleCat.{max u v w z} R :=
    ModuleCat.BalancedTensor.Left.functor k R R M
  let T : ModuleCat.{max u v z} R ⥤ ModuleCat.{max u v w z} R :=
    (ModuleCat.tensorBifunctorAt R).obj (ModuleCat.of R M)
  let V : ModuleCat.{max u v w z} R ⥤ ModuleCat.{max u v w z} k :=
    ModuleCat.restrictScalars (algebraMap k R)
  let e : F ≅ T ⋙ V :=
    (ModuleCat.BalancedTensor.Left.groundIso k R R M
      (hSQ := originalLeftGroundTower (k := k) (R := R) (M := M))).symm ≪≫
      Functor.isoWhiskerRight
        (ModuleCat.BalancedTensor.commutativeCoefficientTensorNatIso.{u, v, w, z} k R M hOp) V
  let P := projectiveResolution X
  let C : ChainComplex (ModuleCat.{max u v w z} R) ℕ :=
    (T.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
  let CV : ChainComplex (ModuleCat.{max u v w z} k) ℕ :=
    (V.mapHomologicalComplex (ComplexShape.down ℕ)).obj C
  let CF : ChainComplex (ModuleCat.{max u v w z} k) ℕ :=
    (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
  let ec : CF ≅ CV := HomologicalComplex.Hom.isoOfComponents
    (fun i => e.app (P.complex.X i)) (by
      intro i j hij
      exact (e.hom.naturality (P.complex.d i j)).symm)
  have hD : IsZero ((T.leftDerived (n + 1)).obj X) :=
    ModuleCat.FlatTensorAcyclic.isZero_leftDerived_obj_of_projectiveResolution.{v, w, max u z}
      R (ModuleCat.of R M) X P n
  have hC : IsZero (C.homology (n + 1)) :=
    IsZero.of_iso hD (P.isoLeftDerivedObj T (n + 1)).symm
  have hCE : C.ExactAt (n + 1) :=
    (HomologicalComplex.exactAt_iff_isZero_homology C (n + 1)).mpr hC
  have hSC : (C.sc' (n + 2) (n + 1) n).Exact :=
    (C.exactAt_iff' (n + 2) (n + 1) n
      (ComplexShape.prev_eq' _ (show (ComplexShape.down ℕ).Rel (n + 2) (n + 1) from rfl))
      (ComplexShape.next_eq' _ (show (ComplexShape.down ℕ).Rel (n + 1) n from rfl))).mp hCE
  have hSVC : (CV.sc' (n + 2) (n + 1) n).Exact :=
    ModuleCat.restrictScalars_map_exact (algebraMap k R) (C.sc' (n + 2) (n + 1) n) hSC
  have hCVE : CV.ExactAt (n + 1) :=
    (CV.exactAt_iff' (n + 2) (n + 1) n
      (ComplexShape.prev_eq' _ (show (ComplexShape.down ℕ).Rel (n + 2) (n + 1) from rfl))
      (ComplexShape.next_eq' _ (show (ComplexShape.down ℕ).Rel (n + 1) n from rfl))).mpr hSVC
  have hCV : IsZero (CV.homology (n + 1)) := hCVE.isZero_homology
  have hCF : IsZero (CF.homology (n + 1)) := IsZero.of_iso hCV
    ((HomologicalComplex.homologyFunctor (ModuleCat.{max u v w z} k)
      (ComplexShape.down ℕ) (n + 1)).mapIso ec)
  exact IsZero.of_iso hCF (P.isoLeftDerivedObj F (n + 1))

/-- The actual native scalar-induced image of an original flat ground target is flat over the acting ring. -/
theorem inducedTarget_flat (N : ModuleCat.{max u v z} k) [Module.Flat k N] :
    Module.Flat R ((ModuleCat.extendScalars.{u, v, max u v z} (algebraMap k R)).obj N) := by
  let φ := algebraMap k R
  let : Algebra k R := φ.toAlgebra
  let : Module k R := φ.toModule
  change Module.Flat R ((ModuleCat.extendScalars.{u, v, max u v z} φ).obj N)
  unfold ModuleCat.extendScalars ModuleCat.ExtendScalars.obj'
  change Module.Flat R (R ⊗[k] N)
  exact Module.Flat.baseChange k R N

/-- Positive derived balanced tensor vanishes on the actual scalar-induced flat target,
with the original coefficient carrier and original right and ground actions. -/
theorem isZero_leftDerived_induced_flat_target (N : ModuleCat.{max u v z} k)
    [Module.Flat k N] (n : ℕ) :
    letI : Small.{max u v z} R := Small.mk'
      ((Equiv.ulift : ULift.{max u z} R ≃ R).symm)
    letI : EnoughProjectives (ModuleCat.{max u v z} R) :=
      @ModuleCat.enoughProjectives.{max u v z, v} R _ inferInstance
    letI : HasProjectiveResolutions (ModuleCat.{max u v z} R) :=
      ⟨fun _ => inferInstance⟩
    IsZero (((ModuleCat.BalancedTensor.functor k R M :
      ModuleCat.{max u v z} R ⥤ ModuleCat.{max u v w z} k).leftDerived (n + 1)).obj
        ((ModuleCat.extendScalars.{u, v, max u v z} (algebraMap k R)).obj N)) := by
  let : Small.{max u v z} R := Small.mk'
    ((Equiv.ulift : ULift.{max u z} R ≃ R).symm)
  let : EnoughProjectives (ModuleCat.{max u v z} R) :=
    @ModuleCat.enoughProjectives.{max u v z, v} R _ inferInstance
  let : HasProjectiveResolutions (ModuleCat.{max u v z} R) :=
    ⟨fun _ => inferInstance⟩
  let : Module.Flat R
      ((ModuleCat.extendScalars.{u, v, max u v z} (algebraMap k R)).obj N) :=
    inducedTarget_flat k R N
  exact isZero_leftDerived_flat_target k R M _ n

end ModuleCat.BalancedTensor.InducedFlatAcyclic
