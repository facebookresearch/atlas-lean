/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.UniversalEnveloping.LeftCochain
public import Mathlib.Algebra.Lie.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Degree-zero Chevalley–Eilenberg cohomology and invariants

Evaluation at the empty exterior word identifies degree-zero cocycles with
the maximal trivial Lie submodule. The cochain homology-to-cycles isomorphism
then identifies degree-zero cohomology with invariants.

The linear equivalence keeps the coefficient carrier. The categorical
comparison lifts it to the cochain universe. The results hold for arbitrary
Lie modules over a commutative ring.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped ModuleCat.Algebra

universe u u' v w w' w'' v'

namespace ChevalleyEilenberg

attribute [local implicit_reducible] leftCoefficientCochainComplex

variable (R : Type u) [CommRing R]
  (L : Type v) [LieRing L] [LieAlgebra R L]
  (M : ModuleCat.{w} (UniversalEnvelopingAlgebra R L))

local notation "U" => UniversalEnvelopingAlgebra R L
local notation "empty" => exteriorPower.ιMulti R 0 (Fin.elim0 : Fin 0 → L)

/-- Native invariants of the original left coefficient module, on its original carrier. -/
abbrev leftCoefficientInvariants :=
  LieModule.maxTrivSubmodule R L (LieModuleCat.UniversalEnveloping.restrictObj R L M)

/-- Degree-zero exterior cochains have their coefficient coordinate. -/
def leftCochainZeroEquiv : ((⋀[R]^0 L) →ₗ[R] M) ≃ₗ[R] M where
  toFun f := f empty
  invFun m := (exteriorPower.zeroEquiv R L).toLinearMap.smulRight m
  left_inv f := by
    apply LinearMap.ext
    intro a
    change exteriorPower.zeroEquiv R L a • f empty = f a
    have ha : exteriorPower.zeroEquiv R L a • empty = a := by
      apply (exteriorPower.zeroEquiv R L).injective
      rw [map_smul, exteriorPower.zeroEquiv_ιMulti, smul_eq_mul, mul_one]
    exact (f.map_smul _ _).symm.trans (congrArg f ha)
  right_inv m := by
    change exteriorPower.zeroEquiv R L empty • m = m
    rw [exteriorPower.zeroEquiv_ιMulti, one_smul]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem leftCochainZeroEquiv_apply (f : (⋀[R]^0 L) →ₗ[R] M) :
    leftCochainZeroEquiv R L M f = f empty := rfl

@[simp]
theorem leftCochainZeroEquiv_symm_apply (m : M) (a : ⋀[R]^0 L) :
    (leftCochainZeroEquiv R L M).symm m a = exteriorPower.zeroEquiv R L a • m := rfl

/-- The first coboundary vanishes exactly when its empty-word value is invariant. -/
theorem leftCochainDifferential_zero_eq_zero_iff (f : (⋀[R]^0 L) →ₗ[R] M) :
    leftCochainDifferential R L M 0 f = 0 ↔
      ∀ x : L, UniversalEnvelopingAlgebra.ι R x • f empty = 0 := by
  constructor
  · intro hf x
    have h : leftCochainDifferential R L M 0 f
        (exteriorPower.ιMulti R 1 (fun _ => x)) = 0 :=
      congrArg (fun g : (⋀[R]^1 L) →ₗ[R] M =>
        g (exteriorPower.ιMulti R 1 (fun _ => x))) hf
    exact (leftCochainDifferential_zero_apply R L M f x).symm.trans h
  · intro hf
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro a
    change leftCochainDifferential R L M 0 f (exteriorPower.ιMulti R 1 a) = 0
    have ha : a = fun _ : Fin 1 => a 0 := by
      funext i
      exact congrArg a (Fin.eq_zero i)
    rw [ha]
    exact (leftCochainDifferential_zero_apply R L M f (a 0)).trans (hf (a 0))

/-- Membership in the native degree-zero cycle kernel is the generator-action condition. -/
theorem leftCochainZeroKernel_iff (f : (⋀[R]^0 L) →ₗ[R] M) :
    f ∈ ((leftCoefficientCochainComplex R L M).sc 0).g.hom.ker ↔
      ∀ x : L, UniversalEnvelopingAlgebra.ι R x • f empty = 0 := by
  change (((leftCoefficientCochainComplex R L M).d 0 ((ComplexShape.up ℕ).next 0)).hom f = 0) ↔ _
  rw [CochainComplex.next, leftCoefficientCochainComplex_d_succ R L M 0]
  exact leftCochainDifferential_zero_eq_zero_iff R L M f

/-- The native outgoing kernel and native invariants have the empty-word coordinates. -/
def leftCochainZeroKernelEquiv : ((leftCoefficientCochainComplex R L M).sc 0).g.hom.ker ≃ₗ[R]
  leftCoefficientInvariants R L M where
  toFun f := ⟨leftCochainZeroEquiv R L M (show (⋀[R]^0 L) →ₗ[R] M from f.1), by
    rw [LieModule.mem_maxTrivSubmodule]
    intro x
    exact (LieModuleCat.UniversalEnveloping.restrictObj_lie R L M x ((show (⋀[R]^0 L) →ₗ[R] M from f.1) empty)).trans
      ((leftCochainZeroKernel_iff R L M (show (⋀[R]^0 L) →ₗ[R] M from f.1)).mp f.property x)⟩
  invFun m := ⟨(leftCochainZeroEquiv R L M).symm (show M from m.1), by
    apply (leftCochainZeroKernel_iff R L M _).mpr
    intro x
    change UniversalEnvelopingAlgebra.ι R x •
      (leftCochainZeroEquiv R L M ((leftCochainZeroEquiv R L M).symm (show M from m.1))) = 0
    rw [LinearEquiv.apply_symm_apply]
    exact (LieModuleCat.UniversalEnveloping.restrictObj_lie R L M x (show M from m.1)).symm.trans
      (m.property x)⟩
  left_inv f := Subtype.ext ((leftCochainZeroEquiv R L M).symm_apply_apply (show (⋀[R]^0 L) →ₗ[R] M from f.1))
  right_inv m := Subtype.ext ((leftCochainZeroEquiv R L M).apply_symm_apply (show M from m.1))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem leftCochainZeroKernelEquiv_coe (f : ((leftCoefficientCochainComplex R L M).sc 0).g.hom.ker) :
    (leftCochainZeroKernelEquiv R L M f).1 = (show (⋀[R]^0 L) →ₗ[R] M from f.1) empty := rfl

/-- Native degree-zero homology identifies with the kernel of the outgoing coboundary. -/
def leftCohomologyZeroKernelEquiv :
    (leftCoefficientCochainComplex R L M).homology 0 ≃ₗ[R] ((leftCoefficientCochainComplex R L M).sc 0).g.hom.ker :=
  ((leftCoefficientCochainComplex R L M).isoHomologyπ₀.symm ≪≫
    ((leftCoefficientCochainComplex R L M).sc 0).moduleCatCyclesIso).toLinearEquiv

/-- H⁰ of the all-degree left CE complex is the native invariant submodule.
The ring, Lie algebra, and original coefficient carrier worlds are independent. -/
def leftCoefficientCohomologyZeroLinearEquiv :
    (leftCoefficientCochainComplex R L M).homology 0 ≃ₗ[R] leftCoefficientInvariants R L M :=
  (leftCohomologyZeroKernelEquiv R L M).trans (leftCochainZeroKernelEquiv R L M)

/-- A native invariant gives the canonical degree-zero cocycle class. -/
def leftCoefficientCohomologyZeroClass (m : leftCoefficientInvariants R L M) :
  (leftCoefficientCochainComplex R L M).homology 0 :=
  (leftCoefficientCochainComplex R L M).homologyπ 0 (((leftCoefficientCochainComplex R L M).sc 0).moduleCatCyclesIso.inv
    ((leftCochainZeroKernelEquiv R L M).symm m))

/-- Canonical native cycles retain their empty-word value in cohomology. -/
theorem leftCoefficientCohomologyZeroLinearEquiv_cycle (f : ((leftCoefficientCochainComplex R L M).sc 0).g.hom.ker) :
    leftCoefficientCohomologyZeroLinearEquiv R L M
        ((leftCoefficientCochainComplex R L M).homologyπ 0
          (((leftCoefficientCochainComplex R L M).sc 0).moduleCatCyclesIso.inv f)) =
      leftCochainZeroKernelEquiv R L M f := by
  let e := (leftCoefficientCochainComplex R L M).isoHomologyπ₀
  let q := ((leftCoefficientCochainComplex R L M).sc 0).moduleCatCyclesIso
  change leftCochainZeroKernelEquiv R L M
    (q.toLinearEquiv (e.toLinearEquiv.symm (e.toLinearEquiv (q.toLinearEquiv.symm f)))) = _
  have h₁ := e.toLinearEquiv.symm_apply_apply (q.toLinearEquiv.symm f)
  have h₂ := q.toLinearEquiv.apply_symm_apply f
  exact (congrArg (fun x => leftCochainZeroKernelEquiv R L M (q.toLinearEquiv x)) h₁).trans
    (congrArg (leftCochainZeroKernelEquiv R L M) h₂)

@[simp]
theorem leftCoefficientCohomologyZeroLinearEquiv_class (m : leftCoefficientInvariants R L M) :
    leftCoefficientCohomologyZeroLinearEquiv R L M
      (leftCoefficientCohomologyZeroClass R L M m) = m := by
  exact (leftCoefficientCohomologyZeroLinearEquiv_cycle R L M
    ((leftCochainZeroKernelEquiv R L M).symm m)).trans
      ((leftCochainZeroKernelEquiv R L M).apply_symm_apply m)

theorem leftCoefficientCohomologyZeroLinearEquiv_symm (m : leftCoefficientInvariants R L M) :
    (leftCoefficientCohomologyZeroLinearEquiv R L M).symm m =
      leftCoefficientCohomologyZeroClass R L M m := by
  apply (leftCoefficientCohomologyZeroLinearEquiv R L M).injective
  rw [LinearEquiv.apply_symm_apply, leftCoefficientCohomologyZeroLinearEquiv_class]

/-- Only the categorical comparison canonically lifts the original invariant carrier. -/
def leftCoefficientCohomologyZeroIso :
    (leftCoefficientCochainComplex R L M).homology 0 ≅ ModuleCat.of R
      (ULift.{max u v w, w} (leftCoefficientInvariants R L M)) :=
  ((leftCoefficientCohomologyZeroLinearEquiv R L M).trans ULift.moduleEquiv.symm).toModuleIso

@[simp]
theorem leftCoefficientCohomologyZeroIso_class (m : leftCoefficientInvariants R L M) :
    (leftCoefficientCohomologyZeroIso R L M).hom
      (leftCoefficientCohomologyZeroClass R L M m) = ULift.up m :=
  congrArg ULift.up (leftCoefficientCohomologyZeroLinearEquiv_class R L M m)

section CoefficientMaps

variable {M} {M' : ModuleCat.{w'} (UniversalEnvelopingAlgebra R L)}
  {M'' : ModuleCat.{w''} (UniversalEnvelopingAlgebra R L)}

/-- An original UEA-linear coefficient map restricts to the native Lie-module map.
Its source and target carriers need not belong to the same module-category universe. -/
def leftCoefficientLieMap (f : M →ₗ[U] M') :
    LieModuleCat.UniversalEnveloping.restrictObj R L M →ₗ⁅R,L⁆
      LieModuleCat.UniversalEnveloping.restrictObj R L M' where
  toLinearMap := f.restrictScalars R
  map_lie' := by
    intro x m
    rw [LieModuleCat.UniversalEnveloping.restrictObj_lie,
      LieModuleCat.UniversalEnveloping.restrictObj_lie]
    exact f.map_smul (UniversalEnvelopingAlgebra.ι R x) m

/-- The native maximal-trivial-submodule map on original coefficients. -/
def leftCoefficientInvariantsMap (f : M →ₗ[U] M') :
    leftCoefficientInvariants R L M →ₗ[R] leftCoefficientInvariants R L M' :=
  (LieModule.maxTrivHom (leftCoefficientLieMap R L f)).toLinearMap

@[simp]
theorem leftCoefficientInvariantsMap_coe (f : M →ₗ[U] M')
    (m : leftCoefficientInvariants R L M) :
    (leftCoefficientInvariantsMap R L f m).1 = f (show M from m.1) := rfl

@[simp]
theorem leftCoefficientInvariantsMap_id :
    leftCoefficientInvariantsMap R L (LinearMap.id : M →ₗ[U] M) = LinearMap.id := by
  apply LinearMap.ext
  intro m
  exact Subtype.ext rfl

theorem leftCoefficientInvariantsMap_comp (f : M →ₗ[U] M') (g : M' →ₗ[U] M'') :
    leftCoefficientInvariantsMap R L (g.comp f) =
      (leftCoefficientInvariantsMap R L g).comp (leftCoefficientInvariantsMap R L f) := by
  apply LinearMap.ext
  intro m
  exact Subtype.ext rfl

/-- The degree-zero cochain map is coefficient postcomposition. -/
def leftCochainZeroCoefficientMap (f : M →ₗ[U] M') :
    ((⋀[R]^0 L) →ₗ[R] M) →ₗ[R] ((⋀[R]^0 L) →ₗ[R] M') where
  toFun a := (f.restrictScalars R).comp a
  map_add' a b := by
    apply LinearMap.ext
    intro z
    exact f.map_add (a z) (b z)
  map_smul' r a := by
    apply LinearMap.ext
    intro z
    exact (f.restrictScalars R).map_smul r (a z)

@[simp]
theorem leftCochainZeroCoefficientMap_apply (f : M →ₗ[U] M')
    (a : (⋀[R]^0 L) →ₗ[R] M) (z : ⋀[R]^0 L) :
    leftCochainZeroCoefficientMap R L f a z = f (a z) := rfl

/-- UEA coefficient maps descend to the outgoing kernels.
The kernel condition is proved from the original generator action, not assumed. -/
def leftCochainZeroCoefficientKernelMap (f : M →ₗ[U] M') :
    ((leftCoefficientCochainComplex R L M).sc 0).g.hom.ker →ₗ[R]
      ((leftCoefficientCochainComplex R L M').sc 0).g.hom.ker where
  toFun a := ⟨leftCochainZeroCoefficientMap R L f (show (⋀[R]^0 L) →ₗ[R] M from a.1), by
    apply (leftCochainZeroKernel_iff R L M' _).mpr
    intro x
    change UniversalEnvelopingAlgebra.ι R x • f ((show (⋀[R]^0 L) →ₗ[R] M from a.1) empty) = 0
    exact (f.map_smul (UniversalEnvelopingAlgebra.ι R x) ((show (⋀[R]^0 L) →ₗ[R] M from a.1) empty)).symm.trans
      ((congrArg f ((leftCochainZeroKernel_iff R L M (show (⋀[R]^0 L) →ₗ[R] M from a.1)).mp a.property x)).trans
        f.map_zero)⟩
  map_add' a b := Subtype.ext ((leftCochainZeroCoefficientMap R L f).map_add a.1 b.1)
  map_smul' r a := Subtype.ext ((leftCochainZeroCoefficientMap R L f).map_smul r a.1)

/-- Empty-word evaluation intertwines the coefficient kernel and invariant maps. -/
theorem leftCochainZeroKernelEquiv_coefficient (f : M →ₗ[U] M')
    (a : ((leftCoefficientCochainComplex R L M).sc 0).g.hom.ker) :
    leftCochainZeroKernelEquiv R L M' (leftCochainZeroCoefficientKernelMap R L f a) =
      leftCoefficientInvariantsMap R L f (leftCochainZeroKernelEquiv R L M a) :=
  Subtype.ext rfl

@[simp]
theorem leftCochainZeroCoefficientKernelMap_id :
    leftCochainZeroCoefficientKernelMap R L (LinearMap.id : M →ₗ[U] M) = LinearMap.id := by
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  apply LinearMap.ext
  intro z
  rfl

theorem leftCochainZeroCoefficientKernelMap_comp (f : M →ₗ[U] M') (g : M' →ₗ[U] M'') :
    leftCochainZeroCoefficientKernelMap R L (g.comp f) =
      (leftCochainZeroCoefficientKernelMap R L g).comp
        (leftCochainZeroCoefficientKernelMap R L f) := by
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  apply LinearMap.ext
  intro z
  rfl

/-- The coefficient map on H⁰ induced by its native cycle-kernel map.
Only the canonical native homology/cycles comparisons are used here. -/
def leftCohomologyZeroCoefficientMap (f : M →ₗ[U] M') :
    (leftCoefficientCochainComplex R L M).homology 0 →ₗ[R]
      (leftCoefficientCochainComplex R L M').homology 0 :=
  (leftCohomologyZeroKernelEquiv R L M').symm.toLinearMap.comp
    ((leftCochainZeroCoefficientKernelMap R L f).comp
      (leftCohomologyZeroKernelEquiv R L M).toLinearMap)

/-- The canonical H⁰ comparison is natural for independently sized original coefficient maps. -/
theorem leftCoefficientCohomologyZeroLinearEquiv_naturality (f : M →ₗ[U] M')
    (a : (leftCoefficientCochainComplex R L M).homology 0) :
    leftCoefficientCohomologyZeroLinearEquiv R L M'
        (leftCohomologyZeroCoefficientMap R L f a) =
      leftCoefficientInvariantsMap R L f (leftCoefficientCohomologyZeroLinearEquiv R L M a) := by
  change leftCochainZeroKernelEquiv R L M'
    ((leftCohomologyZeroKernelEquiv R L M')
      ((leftCohomologyZeroKernelEquiv R L M').symm
        (leftCochainZeroCoefficientKernelMap R L f (leftCohomologyZeroKernelEquiv R L M a)))) = _
  rw [LinearEquiv.apply_symm_apply]
  exact leftCochainZeroKernelEquiv_coefficient R L f (leftCohomologyZeroKernelEquiv R L M a)

@[simp]
theorem leftCohomologyZeroCoefficientMap_id :
    leftCohomologyZeroCoefficientMap R L (LinearMap.id : M →ₗ[U] M) = LinearMap.id := by
  apply LinearMap.ext
  intro a
  change (leftCohomologyZeroKernelEquiv R L M).symm
    (leftCochainZeroCoefficientKernelMap R L LinearMap.id
      (leftCohomologyZeroKernelEquiv R L M a)) = a
  rw [leftCochainZeroCoefficientKernelMap_id, LinearMap.id_apply]
  exact (leftCohomologyZeroKernelEquiv R L M).symm_apply_apply a

theorem leftCohomologyZeroCoefficientMap_comp (f : M →ₗ[U] M') (g : M' →ₗ[U] M'') :
    leftCohomologyZeroCoefficientMap R L (g.comp f) =
      (leftCohomologyZeroCoefficientMap R L g).comp (leftCohomologyZeroCoefficientMap R L f) := by
  apply LinearMap.ext
  intro a
  change (leftCohomologyZeroKernelEquiv R L M'').symm
      (leftCochainZeroCoefficientKernelMap R L (g.comp f) (leftCohomologyZeroKernelEquiv R L M a)) =
    (leftCohomologyZeroKernelEquiv R L M'').symm
      (leftCochainZeroCoefficientKernelMap R L g
        ((leftCohomologyZeroKernelEquiv R L M')
          ((leftCohomologyZeroKernelEquiv R L M').symm
            (leftCochainZeroCoefficientKernelMap R L f (leftCohomologyZeroKernelEquiv R L M a)))))
  rw [LinearEquiv.apply_symm_apply]
  exact congrArg (leftCohomologyZeroKernelEquiv R L M'').symm
    (LinearMap.congr_fun (leftCochainZeroCoefficientKernelMap_comp R L f g)
      (leftCohomologyZeroKernelEquiv R L M a))

@[simp]
theorem leftCohomologyZeroCoefficientMap_class (f : M →ₗ[U] M')
    (m : leftCoefficientInvariants R L M) :
    leftCohomologyZeroCoefficientMap R L f (leftCoefficientCohomologyZeroClass R L M m) =
      leftCoefficientCohomologyZeroClass R L M' (leftCoefficientInvariantsMap R L f m) := by
  apply (leftCoefficientCohomologyZeroLinearEquiv R L M').injective
  rw [leftCoefficientCohomologyZeroLinearEquiv_naturality,
    leftCoefficientCohomologyZeroLinearEquiv_class, leftCoefficientCohomologyZeroLinearEquiv_class]

end CoefficientMaps

/-- The represented/restricted Lie-module unit transports the native invariant submodule. -/
def representedCoefficientInvariantsEquiv (X : LieModuleCat.{w} R L) :
    leftCoefficientInvariants R L (LieModuleCat.UniversalEnveloping.representObj R L X) ≃ₗ[R]
      LieModule.maxTrivSubmodule R L X :=
  LinearEquiv.ofLinearMap
    (LieModule.maxTrivHom ((LieModuleCat.UniversalEnveloping.unitIso R L X).inv)).toLinearMap
    (LieModule.maxTrivHom ((LieModuleCat.UniversalEnveloping.unitIso R L X).hom)).toLinearMap
    (by apply LinearMap.ext; intro m; apply Subtype.ext; rfl)
    (by apply LinearMap.ext; intro m; apply Subtype.ext; rfl)

/-- Arbitrary native Lie coefficients use their represented UEA module, with the
original carrier retained by the native representation/restriction unit. -/
def coefficientCohomologyZeroLinearEquiv (X : LieModuleCat.{w} R L) :
    (leftCoefficientCochainComplex R L
      (LieModuleCat.UniversalEnveloping.representObj R L X)).homology 0 ≃ₗ[R]
        LieModule.maxTrivSubmodule R L X :=
  (leftCoefficientCohomologyZeroLinearEquiv R L
    (LieModuleCat.UniversalEnveloping.representObj R L X)).trans
      (representedCoefficientInvariantsEquiv R L X)

/-- Native Lie coefficients have the same canonical categorical comparison,
using only the native lift of their original invariant carrier. -/
def coefficientCohomologyZeroIso (X : LieModuleCat.{w} R L) :
    (leftCoefficientCochainComplex R L
      (LieModuleCat.UniversalEnveloping.representObj R L X)).homology 0 ≅
        ModuleCat.of R (ULift.{max u v w, w} (LieModule.maxTrivSubmodule R L X)) :=
  ((coefficientCohomologyZeroLinearEquiv R L X).trans ULift.moduleEquiv.symm).toModuleIso

section RingMaps

variable {M} {S : Type u'} [CommRing S]
  {J : Type v'} [LieRing J] [LieAlgebra S J]
  (σ : R →+* S) (φ : L →ₗ⁅ℤ⁆ J)
  (τ : UniversalEnvelopingAlgebra R L →+* UniversalEnvelopingAlgebra S J)
  (hτR : ∀ r : R, τ (algebraMap R (UniversalEnvelopingAlgebra R L) r) =
    algebraMap S (UniversalEnvelopingAlgebra S J) (σ r))
  (hτL : ∀ x : L, τ (UniversalEnvelopingAlgebra.ι R x) =
    UniversalEnvelopingAlgebra.ι S (φ x))
  (N : ModuleCat.{w'} (UniversalEnvelopingAlgebra S J))
  (g : ((ModuleCat.restrictScalars τ).obj N) →ₗ[UniversalEnvelopingAlgebra R L] M)

local notation "emptyJ" => exteriorPower.ιMulti S 0 (Fin.elim0 : Fin 0 → J)

/-- Restriction of the UEA coefficient map to the original ground rings.
The only compatibility used is the scalar characteristic equation for τ. -/
def leftCohomologyRingCoefficientMap :
    letI : Module R N := Module.compHom N σ
    N →ₗ[R] M := by
  letI : Module R N := Module.compHom N σ
  exact
    { toFun := fun n : N => g (show (ModuleCat.restrictScalars τ).obj N from n)
      map_add' := by
        intro n m
        exact g.map_add n m
      map_smul' := by
        intro r n
        let n₀ : (ModuleCat.restrictScalars τ).obj N := n
        have h := g.map_smul (algebraMap R U r) n₀
        have hScalar : τ (algebraMap R U r) = algebraMap S (UniversalEnvelopingAlgebra S J) (σ r) := hτR r
        exact (congrArg (fun a : UniversalEnvelopingAlgebra S J =>
          g (show (ModuleCat.restrictScalars τ).obj N from a • (show N from n))) hScalar).symm.trans h }

/-- The zero-cochain restriction map uses empty-word coordinates and the
given original coefficient map. No cohomology or invariant comparison is an input. -/
def leftCochainZeroRingMap :
    letI : Module R (((⋀[S]^0 J) →ₗ[S] N)) :=
      Module.compHom (((⋀[S]^0 J) →ₗ[S] N)) σ
    (((⋀[S]^0 J) →ₗ[S] N)) →ₗ[R] ((⋀[R]^0 L) →ₗ[R] M) := by
  letI : Module R N := Module.compHom N σ
  letI : Module R (((⋀[S]^0 J) →ₗ[S] N)) :=
    Module.compHom (((⋀[S]^0 J) →ₗ[S] N)) σ
  let c := leftCohomologyRingCoefficientMap (R := R) (L := L) (M := M) (S := S) (J := J) σ τ hτR N g
  refine
    { toFun := fun a => (leftCochainZeroEquiv R L M).symm (c (a emptyJ))
      map_add' := ?_
      map_smul' := ?_ }
  · intro a b
    apply LinearMap.ext
    intro z
    change exteriorPower.zeroEquiv R L z • c (a emptyJ + b emptyJ) =
      exteriorPower.zeroEquiv R L z • c (a emptyJ) +
        exteriorPower.zeroEquiv R L z • c (b emptyJ)
    rw [c.map_add, smul_add]
  · intro r a
    apply LinearMap.ext
    intro z
    change exteriorPower.zeroEquiv R L z • c (r • a emptyJ) =
      r • (exteriorPower.zeroEquiv R L z • c (a emptyJ))
    rw [c.map_smul]
    exact smul_comm _ _ _

/-- Original Lie/ring maps with their UEA scalar and generator equations induce
a map of the zero-cycle kernels. Both rings and all three carrier worlds are independent.
The direction is restriction: cochains on J with N map to cochains on L with M. -/
def leftCochainZeroRingKernelMap :
    letI : Module R ((leftCoefficientCochainComplex S J N).sc 0).g.hom.ker := Module.compHom
      ((leftCoefficientCochainComplex S J N).sc 0).g.hom.ker σ
    ((leftCoefficientCochainComplex S J N).sc 0).g.hom.ker →ₗ[R]
      ((leftCoefficientCochainComplex R L M).sc 0).g.hom.ker := by
  letI : Module R N := Module.compHom N σ
  letI : Module R (((⋀[S]^0 J) →ₗ[S] N)) :=
    Module.compHom (((⋀[S]^0 J) →ₗ[S] N)) σ
  letI : Module R ((leftCoefficientCochainComplex S J N).sc 0).g.hom.ker := Module.compHom
    ((leftCoefficientCochainComplex S J N).sc 0).g.hom.ker σ
  let c := leftCochainZeroRingMap (R := R) (L := L) (M := M) (S := S) (J := J) σ τ hτR N g
  refine
    { toFun := fun a => ⟨c (show (⋀[S]^0 J) →ₗ[S] N from a.1), by
        apply (leftCochainZeroKernel_iff R L M _).mpr
        intro x
        change UniversalEnvelopingAlgebra.ι R x •
          (leftCochainZeroEquiv R L M
            ((leftCochainZeroEquiv R L M).symm (g ((show (⋀[S]^0 J) →ₗ[S] N from a.1) emptyJ)))) = 0
        rw [LinearEquiv.apply_symm_apply]
        have ha := (leftCochainZeroKernel_iff S J N (show (⋀[S]^0 J) →ₗ[S] N from a.1)).mp a.property (φ x)
        calc
          UniversalEnvelopingAlgebra.ι R x • g ((show (⋀[S]^0 J) →ₗ[S] N from a.1) emptyJ) =
              g (τ (UniversalEnvelopingAlgebra.ι R x) • (show (⋀[S]^0 J) →ₗ[S] N from a.1) emptyJ) :=
            (g.map_smul (UniversalEnvelopingAlgebra.ι R x) ((show (⋀[S]^0 J) →ₗ[S] N from a.1) emptyJ)).symm
          _ = g (UniversalEnvelopingAlgebra.ι S (φ x) • (show (⋀[S]^0 J) →ₗ[S] N from a.1) emptyJ) :=
            congrArg (fun z : UniversalEnvelopingAlgebra S J => g (z • (show (⋀[S]^0 J) →ₗ[S] N from a.1) emptyJ))
              (hτL x)
          _ = 0 := (congrArg g ha).trans g.map_zero⟩
      map_add' := fun a b => Subtype.ext (c.map_add a.1 b.1)
      map_smul' := fun r a => Subtype.ext (c.map_smul r a.1) }
/-- Restriction of original invariant values along the same ring/coefficient maps. -/
def leftCoefficientInvariantsRingMap :
    letI : Module R (leftCoefficientInvariants S J N) :=
      Module.compHom (leftCoefficientInvariants S J N) σ
    leftCoefficientInvariants S J N →ₗ[R] leftCoefficientInvariants R L M := by
  letI : Module R N := Module.compHom N σ
  letI : Module R (leftCoefficientInvariants S J N) :=
    Module.compHom (leftCoefficientInvariants S J N) σ
  let c := leftCohomologyRingCoefficientMap (R := R) (L := L) (M := M) (S := S) (J := J) σ τ hτR N g
  refine
    { toFun := fun m => ⟨c (show N from m.1), by
        rw [LieModule.mem_maxTrivSubmodule]
        intro x
        rw [LieModuleCat.UniversalEnveloping.restrictObj_lie]
        have hm : UniversalEnvelopingAlgebra.ι S (φ x) • (show N from m.1) = 0 :=
          (LieModuleCat.UniversalEnveloping.restrictObj_lie S J N (φ x) (show N from m.1)).symm.trans
            (m.property (φ x))
        calc
          UniversalEnvelopingAlgebra.ι R x • g (show N from m.1) =
              g (τ (UniversalEnvelopingAlgebra.ι R x) • (show N from m.1)) :=
            (g.map_smul (UniversalEnvelopingAlgebra.ι R x) (show N from m.1)).symm
          _ = g (UniversalEnvelopingAlgebra.ι S (φ x) • (show N from m.1)) :=
            congrArg (fun z : UniversalEnvelopingAlgebra S J => g (z • (show N from m.1))) (hτL x)
          _ = 0 := (congrArg g hm).trans g.map_zero⟩
      map_add' := fun m n => Subtype.ext (c.map_add m.1 n.1)
      map_smul' := fun r m => Subtype.ext (c.map_smul r m.1) }
/-- The Lie/ring kernel map commutes with native invariant coordinates. -/
theorem leftCochainZeroKernelEquiv_ring_naturality (a : ((leftCoefficientCochainComplex S J N).sc 0).g.hom.ker) :
    leftCochainZeroKernelEquiv R L M
        (leftCochainZeroRingKernelMap R L σ φ τ hτR hτL N g a) =
      leftCoefficientInvariantsRingMap R L σ φ τ hτR hτL N g
        (leftCochainZeroKernelEquiv S J N a) := by
  apply Subtype.ext
  change leftCochainZeroEquiv R L M
    ((leftCochainZeroEquiv R L M).symm
      (g ((show (⋀[S]^0 J) →ₗ[S] N from a.1) emptyJ))) =
        g ((show (⋀[S]^0 J) →ₗ[S] N from a.1) emptyJ)
  exact (leftCochainZeroEquiv R L M).apply_symm_apply _

/-- The H⁰ ring-restriction map is induced by the native kernel map.
The source is the original S-cohomology carrier with its R-action along σ. -/
def leftCohomologyZeroRingMap :
    letI : Module R ((leftCoefficientCochainComplex S J N).homology 0) := Module.compHom
      ((leftCoefficientCochainComplex S J N).homology 0) σ
    (leftCoefficientCochainComplex S J N).homology 0 →ₗ[R] (leftCoefficientCochainComplex R L M).homology 0 := by
  letI : Algebra R S := σ.toAlgebra
  letI : Module R ((leftCoefficientCochainComplex S J N).homology 0) := Module.compHom
    ((leftCoefficientCochainComplex S J N).homology 0) σ
  letI : Module R ((leftCoefficientCochainComplex S J N).sc 0).g.hom.ker := Module.compHom
    ((leftCoefficientCochainComplex S J N).sc 0).g.hom.ker σ
  letI : IsScalarTower R S ((leftCoefficientCochainComplex S J N).homology 0) := IsScalarTower.of_compHom R S
    ((leftCoefficientCochainComplex S J N).homology 0)
  letI : IsScalarTower R S ((leftCoefficientCochainComplex S J N).sc 0).g.hom.ker := IsScalarTower.of_compHom R S
    ((leftCoefficientCochainComplex S J N).sc 0).g.hom.ker
  let eS : (leftCoefficientCochainComplex S J N).homology 0 →ₗ[R]
      ((leftCoefficientCochainComplex S J N).sc 0).g.hom.ker :=
    (leftCohomologyZeroKernelEquiv S J N).toLinearMap.restrictScalars R
  exact (leftCohomologyZeroKernelEquiv R L M).symm.toLinearMap.comp
    ((leftCochainZeroRingKernelMap R L σ φ τ hτR hτL N g).comp eS)

/-- The requested raw H⁰ comparison respects independent-ground Lie/ring restriction. -/
theorem leftCoefficientCohomologyZeroLinearEquiv_ring_naturality
  (a : (leftCoefficientCochainComplex S J N).homology 0) :
    leftCoefficientCohomologyZeroLinearEquiv R L M
        (leftCohomologyZeroRingMap R L σ φ τ hτR hτL N g a) =
      leftCoefficientInvariantsRingMap R L σ φ τ hτR hτL N g
        (leftCoefficientCohomologyZeroLinearEquiv S J N a) := by
  change leftCochainZeroKernelEquiv R L M
    ((leftCohomologyZeroKernelEquiv R L M)
      ((leftCohomologyZeroKernelEquiv R L M).symm
        (leftCochainZeroRingKernelMap R L σ φ τ hτR hτL N g
          (leftCohomologyZeroKernelEquiv S J N a)))) = _
  rw [LinearEquiv.apply_symm_apply]
  exact leftCochainZeroKernelEquiv_ring_naturality R L σ φ τ hτR hτL N g
    (leftCohomologyZeroKernelEquiv S J N a)

@[simp]
theorem leftCohomologyZeroRingMap_class (m : leftCoefficientInvariants S J N) :
    leftCohomologyZeroRingMap R L σ φ τ hτR hτL N g
        (leftCoefficientCohomologyZeroClass S J N m) =
      leftCoefficientCohomologyZeroClass R L M
        (leftCoefficientInvariantsRingMap R L σ φ τ hτR hτL N g m) := by
  apply (leftCoefficientCohomologyZeroLinearEquiv R L M).injective
  rw [leftCoefficientCohomologyZeroLinearEquiv_ring_naturality,
    leftCoefficientCohomologyZeroLinearEquiv_class, leftCoefficientCohomologyZeroLinearEquiv_class]

end RingMaps

end ChevalleyEilenberg
