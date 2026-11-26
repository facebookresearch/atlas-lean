/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.UniversalEnveloping.LeftCochain
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.UniversalEnveloping.Resolution
public import MathlibExt.CategoryTheory.Abelian.LeftDerived.PrecompositionNaturality
public import MathlibExt.CategoryTheory.Abelian.Ext.ProjectiveLinearComparison
public import Mathlib.Algebra.Category.ModuleCat.Ulift

/-!
# Left-coefficient CE cohomology as enveloping linear Ext

For a commutative ring R and an R-Lie algebra L free as an R-module, the enveloping CE complex
is a projective resolution of the trivial left U_R(L)-module. A ULift functor carries that
resolution into the common module-category height H = max u v w, together with a separately
lifted left coefficient module M : Type w.

The down/up coordinate map sends a homomorphism between the lifted modules to z ↦
down(f(up(z))). It identifies the linear Yoneda cochains of the lifted resolution with
Hom_U(C_•,M), and the exterior Hom coordinates identify these with Hom_R(⋀^• L,M).

The resulting cochain homology computes the first-variable R-linear Ext term Ext_U^n(T,M),
with both modules lifted to H. The coefficient module is arbitrary; only the underlying Lie
module is assumed free.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct ModuleCat.Algebra

namespace ChevalleyEilenberg

variable (R : Type u) [CommRing R]
  (L : Type v) [LieRing L] [LieAlgebra R L]

local notation "U" => UniversalEnvelopingAlgebra R L

/-- Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U its enveloping algebra
and C_n = ⋀[R]^n L ⊗[R] U with negative right-regular Lie coefficients. For a coefficient
universe w, envelopingLiftFunctor maps ModuleCat.{max u v} U to ModuleCat.{max u v w} U by the
module ULift functor. It preserves the underlying U-action through the up/down coordinate
equivalence. -/
abbrev envelopingLiftFunctor : ModuleCat.{max u v} U ⥤ (ModuleCat.{max u v w} (UniversalEnvelopingAlgebra R L)) :=
  ModuleCat.uliftFunctor.{w, max u v} U

local instance envelopingLift_preservesHomology :
    (envelopingLiftFunctor.{u, v, w} R L).PreservesHomology := by
  apply Functor.preservesHomology_of_map_exact
  intro S hS
  exact ModuleCat.uliftFunctor_map_exact U S hS

/-- Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U its enveloping algebra
and C_n = ⋀[R]^n L ⊗[R] U with negative right-regular Lie coefficients. For H = max u v w,
liftedEnvelopingTrivial is the image under envelopingLiftFunctor of envelopingTrivialObject R
L. The source scalar module is already ULift R with augmentation action, and the functor
applies its further carrier lift. -/
abbrev liftedEnvelopingTrivial : (ModuleCat.{max u v w} (UniversalEnvelopingAlgebra R L)) :=
  (envelopingLiftFunctor.{u, v, w} R L).obj (envelopingTrivialObject R L)

/-- Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U its enveloping algebra
and C_n = ⋀[R]^n L ⊗[R] U with negative right-regular Lie coefficients. Assume Module.Free R
L. Applying envelopingLiftFunctor to envelopingProjectiveResolution R L gives a
ProjectiveResolution of liftedEnvelopingTrivial in ModuleCat.{max u v w} U. Its complex and
augmentation are the functorial images of the enveloping CE resolution. -/
def liftedEnvelopingProjectiveResolution [Module.Free R L] :
    ProjectiveResolution (liftedEnvelopingTrivial.{u, v, w} R L) :=
  (envelopingLiftFunctor.{u, v, w} R L).mapProjectiveResolution
    (envelopingProjectiveResolution R L)

@[simp]
theorem liftedEnvelopingProjectiveResolution_complex [Module.Free R L] :
    (liftedEnvelopingProjectiveResolution.{u, v, w} R L).complex =
      (((envelopingLiftFunctor.{u, v, w} R L).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (envelopingComplex R L)) := rfl

/-- Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U its enveloping algebra
and C_n = ⋀[R]^n L ⊗[R] U with negative right-regular Lie coefficients. Assume Module.Free R
L. The degree-zero augmentation of liftedEnvelopingProjectiveResolution equals
envelopingLiftFunctor.map ((envelopingAugmentation R L).f 0). -/
theorem liftedEnvelopingProjectiveResolution_π_f_zero [Module.Free R L] :
    (liftedEnvelopingProjectiveResolution.{u, v, w} R L).π.f 0 =
      (envelopingLiftFunctor.{u, v, w} R L).map ((envelopingAugmentation R L).f 0) :=
  ProjectiveResolution.mapProjectiveResolution_π_f_zero (envelopingLiftFunctor.{u, v, w} R L)
    (envelopingProjectiveResolution R L)

variable (M : ModuleCat.{w} (UniversalEnvelopingAlgebra R L))

/-- Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U its enveloping algebra
and C_n = ⋀[R]^n L ⊗[R] U with negative right-regular Lie coefficients. Put h₀ = max u v and H
= max u v w. Let E : ModuleCat.{h₀} U ⥤ ModuleCat.{H} U be the ULift functor, T₀ the scalar
module ULift R acted on through augmentation, and M : ModuleCat.{w} U an arbitrary left
coefficient module. liftedLeftCoefficient is the image of M under ModuleCat.uliftFunctor from
its carrier universe w to H, using the additional lift max u v. It carries the transported
left U-action. -/
abbrev liftedLeftCoefficient : (ModuleCat.{max u v w} (UniversalEnvelopingAlgebra R L)) :=
  (ModuleCat.uliftFunctor.{max u v, w} U).obj M

/-- Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U its enveloping algebra
and C_n = ⋀[R]^n L ⊗[R] U with negative right-regular Lie coefficients. Put h₀ = max u v and H
= max u v w. Let E : ModuleCat.{h₀} U ⥤ ModuleCat.{H} U be the ULift functor, T₀ the scalar
module ULift R acted on through augmentation, and M : ModuleCat.{w} U an arbitrary left
coefficient module. For n : ℕ, liftedEnvelopingHomCoordinates is an R-linear equivalence
Hom_U(E(C_n),liftedLeftCoefficient M) ≃ₗ[R] Hom_U(C_n,M). Its forward map sends f to z ↦
down(f(up(z))); its inverse sends a map a to the module morphism up(z) ↦ up(a(z)). -/
def liftedEnvelopingHomCoordinates (n : ℕ) :
    ((envelopingLiftFunctor.{u, v, w} R L).obj ((envelopingComplex R L).X n) ⟶
      liftedLeftCoefficient R L M) ≃ₗ[R] envelopingHomTerm R L M n where
  toFun f :=
    (ULift.moduleEquiv : ULift.{max u v} M ≃ₗ[U] M).toLinearMap.comp
      (f.hom.comp
        (ULift.moduleEquiv : ULift.{w} ((envelopingComplex R L).X n) ≃ₗ[U]
          (envelopingComplex R L).X n).symm.toLinearMap)
  invFun f := ModuleCat.ofHom
    ((ULift.moduleEquiv : ULift.{max u v} M ≃ₗ[U] M).symm.toLinearMap.comp
      (f.comp
        (ULift.moduleEquiv : ULift.{w} ((envelopingComplex R L).X n) ≃ₗ[U]
          (envelopingComplex R L).X n).toLinearMap))
  left_inv f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply ULift.ext
    rfl
  right_inv f := by apply LinearMap.ext; intro z; rfl
  map_add' f g := by apply LinearMap.ext; intro z; rfl
  map_smul' r f := by apply LinearMap.ext; intro z; rfl

theorem liftedEnvelopingHomCoordinates_apply (n : ℕ)
    (f : (envelopingLiftFunctor.{u, v, w} R L).obj ((envelopingComplex R L).X n) ⟶
      liftedLeftCoefficient R L M) (z : (envelopingComplex R L).X n) :
    liftedEnvelopingHomCoordinates R L M n f z = (f.hom (ULift.up z)).down := rfl

/-- Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U its enveloping algebra
and C_n = ⋀[R]^n L ⊗[R] U with negative right-regular Lie coefficients. Put h₀ = max u v and H
= max u v w. Let E : ModuleCat.{h₀} U ⥤ ModuleCat.{H} U be the ULift functor, T₀ the scalar
module ULift R acted on through augmentation, and M : ModuleCat.{w} U an arbitrary left
coefficient module. Assume Module.Free R L. liftedEnvelopingHomComplex is the ℕ-indexed
R-module cochain complex obtained by applying the linear Yoneda functor
Hom_U(−,liftedLeftCoefficient M) to the lifted projective resolution. -/
abbrev liftedEnvelopingHomComplex [Module.Free R L] :
    CochainComplex (ModuleCat.{max u v w} R) ℕ :=
  (liftedEnvelopingProjectiveResolution.{u, v, w} R L).complex.linearYonedaObj R
    (liftedLeftCoefficient R L M)

/-- Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U its enveloping algebra
and C_n = ⋀[R]^n L ⊗[R] U with negative right-regular Lie coefficients. Put h₀ = max u v and H
= max u v w. Let E : ModuleCat.{h₀} U ⥤ ModuleCat.{H} U be the ULift functor, T₀ the scalar
module ULift R acted on through augmentation, and M : ModuleCat.{w} U an arbitrary left
coefficient module. Assume Module.Free R L. For n : ℕ and a lifted cochain f, the differential
from n to n + 1 is P_lift.complex.d (n + 1) n ≫ f. This is positive precomposition, with no
extra degree sign. -/
theorem liftedEnvelopingHomComplex_d_apply [Module.Free R L] (n : ℕ)
    (f : (liftedEnvelopingHomComplex R L M).X n) :
    ((liftedEnvelopingHomComplex R L M).d n (n + 1)).hom f =
      (liftedEnvelopingProjectiveResolution.{u, v, w} R L).complex.d (n + 1) n ≫ f := by
  let P := liftedEnvelopingProjectiveResolution.{u, v, w} R L
  let Y := liftedLeftCoefficient R L M
  have h := P.linearYonedaComplex_g_apply R Y n f
  change ((P.linearYonedaComplex R Y).d n ((ComplexShape.up ℕ).next n)).hom f =
    P.complex.d ((ComplexShape.up ℕ).next n) n ≫ f at h
  have hn : (ComplexShape.up ℕ).next n = n + 1 :=
    ComplexShape.next_eq' _ (ComplexShape.up_mk _ _ rfl)
  rw [hn] at h
  exact h

/-- Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U its enveloping algebra
and C_n = ⋀[R]^n L ⊗[R] U with negative right-regular Lie coefficients. Put h₀ = max u v and H
= max u v w. Let E : ModuleCat.{h₀} U ⥤ ModuleCat.{H} U be the ULift functor, T₀ the scalar
module ULift R acted on through augmentation, and M : ModuleCat.{w} U an arbitrary left
coefficient module. Assume Module.Free R L. The degreewise up/down Hom equivalences give
liftedEnvelopingHomComplex R L M ≅ envelopingHomComplex R L M, with degree-n coordinate f ↦ (z
↦ down(f(up(z)))). The target cochains are U-linear maps C_n → M with boundary precomposition. -/
def liftedEnvelopingHomIso [Module.Free R L] :
    liftedEnvelopingHomComplex R L M ≅ envelopingHomComplex R L M :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (liftedEnvelopingHomCoordinates R L M n).toModuleIso) (by
      intro i j hij
      change i + 1 = j at hij
      subst j
      apply ModuleCat.hom_ext
      rw [envelopingHomComplex_d_succ]
      apply LinearMap.ext
      intro f
      change envelopingHomDifferential R L M i
        (liftedEnvelopingHomCoordinates R L M i f) =
        liftedEnvelopingHomCoordinates R L M (i + 1)
          (((liftedEnvelopingHomComplex R L M).d i (i + 1)).hom f)
      rw [liftedEnvelopingHomComplex_d_apply]
      ext z
      rfl)

/-- Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U its enveloping algebra
and C_n = ⋀[R]^n L ⊗[R] U with negative right-regular Lie coefficients. Put h₀ = max u v and H
= max u v w. Let E : ModuleCat.{h₀} U ⥤ ModuleCat.{H} U be the ULift functor, T₀ the scalar
module ULift R acted on through augmentation, and M : ModuleCat.{w} U an arbitrary left
coefficient module. For n : ℕ, leftEnvelopingExt R L M n is the R-linear Ext module in the
category ModuleCat.{H} U, evaluated contravariantly at E(T₀) and covariantly at
liftedLeftCoefficient M. It is Ext_U^n(E(T₀),liftedLeftCoefficient M). -/
abbrev leftEnvelopingExt (n : ℕ) : ModuleCat.{max u v w} R :=
  ((_root_.Ext R (ModuleCat.{max u v w} (UniversalEnvelopingAlgebra R L)) n).obj
    (op (liftedEnvelopingTrivial.{u, v, w} R L))).obj
    (liftedLeftCoefficient R L M)

/-- Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U its enveloping algebra
and C_n = ⋀[R]^n L ⊗[R] U with negative right-regular Lie coefficients. Put h₀ = max u v and H
= max u v w. Let E : ModuleCat.{h₀} U ⥤ ModuleCat.{H} U be the ULift functor, T₀ the scalar
module ULift R acted on through augmentation, and M : ModuleCat.{w} U an arbitrary left
coefficient module. Assume Module.Free R L. For n : ℕ, leftCoefficientHomologyIsoExt
identifies H^n(leftCoefficientCochainComplex R L M) with leftEnvelopingExt R L M n. The source
has terms Hom_R(⋀[R]^n L,M); the comparison uses its enveloping Hom coordinates, the lift Hom
isomorphism and the projective-resolution Ext comparison. -/
def leftCoefficientHomologyIsoExt [Module.Free R L] (n : ℕ) :
    (leftCoefficientCochainComplex R L M).homology n ≅ leftEnvelopingExt R L M n :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{max u v w} R) (ComplexShape.up ℕ) n).mapIso
    (envelopingHomCoefficientIso R L M).symm ≪≫
      (HomologicalComplex.homologyFunctor (ModuleCat.{max u v w} R) (ComplexShape.up ℕ) n).mapIso
        (liftedEnvelopingHomIso R L M).symm ≪≫
          ((liftedEnvelopingProjectiveResolution.{u, v, w} R L).isoExt (R := R) n
            (liftedLeftCoefficient R L M)).symm

end ChevalleyEilenberg
