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
# Flat targets for balanced tensor functors

Let k and R be commutative rings with a k-algebra structure on R, and let M be a k-module with
a compatible right R-action. Pulling that action back along r ↦ op r equips M with the
corresponding left R-action. The balanced tensor functor from R-modules to k-modules is
naturally isomorphic to M ⊗[R] (−) followed by restriction of scalars.

For a flat R-module X, every positive left-derived object of this functor is zero. If N is
flat over k, its scalar extension R ⊗[k] N is flat over R and therefore has the same vanishing
property. The rings, coefficient module and target modules can have different carrier
universes; the target and value categories are enlarged by the indicated maxima.

See Bourbaki, *Algebra*, Chapter III, and Weibel, *An Introduction to Homological Algebra*,
Chapter 3.
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

/- For commutative R, pulling the right action back along r ↦ op r gives the left action r • m = op r • m. -/
local instance (priority := 10) originalLeftModule : Module R M :=
  Module.compHom M (RingEquiv.toOpposite R).toRingHom

/-- For commutative rings k and R and a module M with commuting k- and right R-actions, the left
action r • m := op r • m also commutes with k: a • (r • m) = r • (a • m) for every a : k, r :
R and m : M. -/
local instance originalLeftGroundComm : SMulCommClass k R M where
  smul_comm a r m := by
    change a • (op r • m) = op r • (a • m)
    exact smul_comm a (op r) m

/-- Let k and R be commutative rings with R a k-algebra, and let the k-action and right R-action
on M form the scalar tower k → Rᵐᵒᵖ → M. For the left action r • m := op r • m, they also form
the tower k → R → M; in particular, algebraMap k R a • m = a • m. -/
local instance originalLeftGroundTower : IsScalarTower k R M :=
  IsScalarTower.of_algebraMap_smul (fun a m => by
    change op (algebraMap k R a) • m = a • m
    simpa only [MulOpposite.algebraMap_apply] using
      (IsScalarTower.algebraMap_smul Rᵐᵒᵖ a m))

/-- For commutative rings k and R and a module M whose k- and right R-actions commute, the left
action r • m := op r • m satisfies r • (a • m) = a • (r • m) for every r : R, a : k and m : M.
This is the commutation law with the R-action written first. -/
local instance originalLeftGroundCommSymm : SMulCommClass R k M := SMulCommClass.symm k R M

attribute [local instance] ModuleCat.BalancedTensor.additive

/-- Let k : Type u and R : Type v be commutative rings, let R be a k-algebra, and let M : Type w
have compatible k- and right R-actions: these actions commute and form the tower k → Rᵐᵒᵖ → M.
For a flat X in ModuleCat.{max u v z} R and every n : ℕ, the object (F.leftDerived (n +
1)).obj X is zero, where F is the balanced tensor functor N ↦ B k R M N with values in
ModuleCat.{max u v w z} k. The smallness and projective-resolution structures in the statement
are supplied by lifting R into the target universe. The coefficient module M is arbitrary. -/
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

/-- For commutative rings k : Type u and R : Type v with R a k-algebra, let N be a flat k-module
in ModuleCat.{max u v z} k. Its scalar extension along algebraMap k R, namely the R-module R
⊗[k] N, is flat over R. -/
theorem inducedTarget_flat (N : ModuleCat.{max u v z} k) [Module.Flat k N] :
    Module.Flat R ((ModuleCat.extendScalars.{u, v, max u v z} (algebraMap k R)).obj N) := by
  let φ := algebraMap k R
  let : Algebra k R := φ.toAlgebra
  let : Module k R := φ.toModule
  change Module.Flat R ((ModuleCat.extendScalars.{u, v, max u v z} φ).obj N)
  unfold ModuleCat.extendScalars ModuleCat.ExtendScalars.obj'
  change Module.Flat R (R ⊗[k] N)
  exact Module.Flat.baseChange k R N

/-- Let k : Type u and R : Type v be commutative rings with R a k-algebra. Let M : Type w have k-
and right R-actions which commute and form the tower k → Rᵐᵒᵖ → M. If N in ModuleCat.{max u v
z} k is flat over k, then for every n : ℕ the (n + 1)-st left-derived object of the balanced
tensor functor F at extendScalars(algebraMap k R).obj N is zero. Here F takes values in
ModuleCat.{max u v w z} k, and the statement supplies the smallness and projective-resolution
structures by lifting R. This vanishing follows for the scalar-induced module R ⊗[k] N. -/
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
