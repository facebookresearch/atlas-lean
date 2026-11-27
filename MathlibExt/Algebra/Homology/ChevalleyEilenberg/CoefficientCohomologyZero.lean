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
# Degree-zero Lie cohomology and invariant coefficients

Let R be commutative, L an R-Lie algebra and M a left module over
U_R=UEA_R(L). Restricting through the generators gives [x,m]=ι_R(x)m.
Evaluation at the empty wedge identifies Hom_R(Λ_R^0L,M) with M.
The first coboundary evaluated at x is ι_R(x)f(1), so its kernel
corresponds to the maximal trivial Lie submodule
M^L={m | ι_R(x)m=0 for all x}.

There is an R-linear equivalence H^0(L,M)≃M^L, with
[f]↦f(1) and m↦[r↦rm]. The invariant carrier remains in its
coefficient universe w; the categorical isomorphism lifts it to
max{u,v,w}. Arbitrary Lie-module coefficients use their canonical
UEA representation and the same invariant comparison.

UEA-linear coefficient maps preserve these coordinates. For a ring map
σ:R→S, an underlying ℤ-Lie map φ:L→J and a UEA ring map τ with
τ(algMap_R r)=algMap_S(σ r), τ(ι_R x)=ι_S(φ x),
a τ-linear coefficient map N→M induces restriction
H^0(J,N)→H^0(L,M). This map sends an invariant value n to g(n);
all ring, Lie and coefficient carrier universes may be independent.

Reference: C. A. Weibel, An Introduction to Homological Algebra, §7.7.
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

/-- Let R:Type u be commutative, L:Type v an R-Lie algebra,
and M a left U=UEA_R(L)-module with carrier universe w.
Its restricted L-action is [x,m]=ι_R(x)•m, and M^L is
{m | ι_R(x)•m=0 for every x∈L}.
The invariant coefficient module is the maximal trivial Lie
submodule M^L of the restricted U-module, on its coefficient carrier. -/
abbrev leftCoefficientInvariants :=
  LieModule.maxTrivSubmodule R L (LieModuleCat.UniversalEnveloping.restrictObj R L M)

/-- Let R:Type u be commutative, L:Type v an R-Lie algebra,
and M a left U=UEA_R(L)-module with carrier universe w.
Its restricted L-action is [x,m]=ι_R(x)•m, and M^L is
{m | ι_R(x)•m=0 for every x∈L}.
Evaluation at the empty wedge gives the R-linear equivalence
Hom_R(Λ_R^0L,M)≃M. Its inverse sends m to the cochain
z↦e_0(z)•m, where e_0:Λ_R^0L≃R. -/
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

/-- Let R:Type u be commutative, L:Type v an R-Lie algebra,
and M a left U=UEA_R(L)-module with carrier universe w.
Its restricted L-action is [x,m]=ι_R(x)•m, and M^L is
{m | ι_R(x)•m=0 for every x∈L}.
For a zero-cochain f, d^0f=0 if and only if
ι_R(x)•f(1)=0 for every x∈L. -/
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

/-- Let R:Type u be commutative, L:Type v an R-Lie algebra,
and M a left U=UEA_R(L)-module with carrier universe w.
Its restricted L-action is [x,m]=ι_R(x)•m, and M^L is
{m | ι_R(x)•m=0 for every x∈L}.
A zero-cochain f belongs to the outgoing differential kernel
if and only if its empty-wedge value f(1) lies in M^L. -/
theorem leftCochainZeroKernel_iff (f : (⋀[R]^0 L) →ₗ[R] M) :
    f ∈ ((leftCoefficientCochainComplex R L M).sc 0).g.hom.ker ↔
      ∀ x : L, UniversalEnvelopingAlgebra.ι R x • f empty = 0 := by
  change (((leftCoefficientCochainComplex R L M).d 0 ((ComplexShape.up ℕ).next 0)).hom f = 0) ↔ _
  rw [CochainComplex.next, leftCoefficientCochainComplex_d_succ R L M 0]
  exact leftCochainDifferential_zero_eq_zero_iff R L M f

/-- Let R:Type u be commutative, L:Type v an R-Lie algebra,
and M a left U=UEA_R(L)-module with carrier universe w.
Its restricted L-action is [x,m]=ι_R(x)•m, and M^L is
{m | ι_R(x)•m=0 for every x∈L}.
Empty-wedge evaluation gives an R-linear equivalence
ker(d^0)≃M^L, sending a cocycle f to f(1). -/
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

/-- Let R:Type u be commutative, L:Type v an R-Lie algebra,
and M a left U=UEA_R(L)-module with carrier universe w.
Its restricted L-action is [x,m]=ι_R(x)•m, and M^L is
{m | ι_R(x)•m=0 for every x∈L}.
There is no incoming degree-zero coboundary in the nonnegative
cochain complex, so H^0(L,M)≃ker(d^0) as R-modules. -/
def leftCohomologyZeroKernelEquiv :
    (leftCoefficientCochainComplex R L M).homology 0 ≃ₗ[R] ((leftCoefficientCochainComplex R L M).sc 0).g.hom.ker :=
  ((leftCoefficientCochainComplex R L M).isoHomologyπ₀.symm ≪≫
    ((leftCoefficientCochainComplex R L M).sc 0).moduleCatCyclesIso).toLinearEquiv

/-- Let R:Type u be commutative, L:Type v an R-Lie algebra,
and M a left U=UEA_R(L)-module with carrier universe w.
Its restricted L-action is [x,m]=ι_R(x)•m, and M^L is
{m | ι_R(x)•m=0 for every x∈L}.
Combining the kernel and empty-wedge identifications gives
H^0(L,M)≃M^L, an R-linear equivalence preserving the coefficient carrier. -/
def leftCoefficientCohomologyZeroLinearEquiv :
    (leftCoefficientCochainComplex R L M).homology 0 ≃ₗ[R] leftCoefficientInvariants R L M :=
  (leftCohomologyZeroKernelEquiv R L M).trans (leftCochainZeroKernelEquiv R L M)

/-- Let R:Type u be commutative, L:Type v an R-Lie algebra,
and M a left U=UEA_R(L)-module with carrier universe w.
Its restricted L-action is [x,m]=ι_R(x)•m, and M^L is
{m | ι_R(x)•m=0 for every x∈L}.
For m∈M^L, the canonical degree-zero cohomology class is
that of the cocycle z↦e_0(z)•m, where e_0:Λ_R^0L≃R. -/
def leftCoefficientCohomologyZeroClass (m : leftCoefficientInvariants R L M) :
  (leftCoefficientCochainComplex R L M).homology 0 :=
  (leftCoefficientCochainComplex R L M).homologyπ 0 (((leftCoefficientCochainComplex R L M).sc 0).moduleCatCyclesIso.inv
    ((leftCochainZeroKernelEquiv R L M).symm m))

/-- Let R:Type u be commutative, L:Type v an R-Lie algebra,
and M a left U=UEA_R(L)-module with carrier universe w.
Its restricted L-action is [x,m]=ι_R(x)•m, and M^L is
{m | ι_R(x)•m=0 for every x∈L}.
The H^0-to-invariants equivalence sends the homology class
of a cocycle f∈ker(d^0) to its invariant empty-wedge value f(1). -/
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

/-- Let R:Type u be commutative, L:Type v an R-Lie algebra,
and M a left U=UEA_R(L)-module with carrier universe w.
Its restricted L-action is [x,m]=ι_R(x)•m, and M^L is
{m | ι_R(x)•m=0 for every x∈L}.
The categorical comparison is
H^0(L,M)≅ModuleCat_R(U^{max{u,v,w}}M^L),
placing the invariant module in the cochain carrier universe. -/
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

/-- Let R:Type u be commutative, L:Type v an R-Lie algebra,
and M a left U=UEA_R(L)-module with carrier universe w.
Its restricted L-action is [x,m]=ι_R(x)•m, and M^L is
{m | ι_R(x)•m=0 for every x∈L}.
Let M′ be another left U-module in an independent carrier universe
and f:M→M′ a U-linear map.
Restricting f to R-scalars gives a Lie-module map, since
f(ι_R(x)m)=ι_R(x)f(m) for every x∈L. -/
def leftCoefficientLieMap (f : M →ₗ[U] M') :
    LieModuleCat.UniversalEnveloping.restrictObj R L M →ₗ⁅R,L⁆
      LieModuleCat.UniversalEnveloping.restrictObj R L M' where
  toLinearMap := f.restrictScalars R
  map_lie' := by
    intro x m
    rw [LieModuleCat.UniversalEnveloping.restrictObj_lie,
      LieModuleCat.UniversalEnveloping.restrictObj_lie]
    exact f.map_smul (UniversalEnvelopingAlgebra.ι R x) m

/-- Let R:Type u be commutative, L:Type v an R-Lie algebra,
and M a left U=UEA_R(L)-module with carrier universe w.
Its restricted L-action is [x,m]=ι_R(x)•m, and M^L is
{m | ι_R(x)•m=0 for every x∈L}.
Let M′ be another left U-module in an independent carrier universe
and f:M→M′ a U-linear map.
The map f carries M^L into M′^L, giving the R-linear
invariant map m↦f(m). -/
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

/-- Let R:Type u be commutative, L:Type v an R-Lie algebra,
and M a left U=UEA_R(L)-module with carrier universe w.
Its restricted L-action is [x,m]=ι_R(x)•m, and M^L is
{m | ι_R(x)•m=0 for every x∈L}.
Let M′ be another left U-module in an independent carrier universe
and f:M→M′ a U-linear map.
The degree-zero cochain map is postcomposition:
a:Λ_R^0L→M is sent to f∘a:Λ_R^0L→M′. -/
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

/-- Let R:Type u be commutative, L:Type v an R-Lie algebra,
and M a left U=UEA_R(L)-module with carrier universe w.
Its restricted L-action is [x,m]=ι_R(x)•m, and M^L is
{m | ι_R(x)•m=0 for every x∈L}.
Let M′ be another left U-module in an independent carrier universe
and f:M→M′ a U-linear map.
Coefficient postcomposition carries ker(d_M^0) into ker(d_{M′}^0),
giving an R-linear map between the zero-cocycle kernels. -/
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

/-- Let R:Type u be commutative, L:Type v an R-Lie algebra,
and M a left U=UEA_R(L)-module with carrier universe w.
Its restricted L-action is [x,m]=ι_R(x)•m, and M^L is
{m | ι_R(x)•m=0 for every x∈L}.
Let M′ be another left U-module in an independent carrier universe
and f:M→M′ a U-linear map.
Empty-wedge kernel evaluation is natural:
E_{M′}(K(f)(a))=f^{inv}(E_M(a)) for every a∈ker(d_M^0). -/
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

/-- Let R:Type u be commutative, L:Type v an R-Lie algebra,
and M a left U=UEA_R(L)-module with carrier universe w.
Its restricted L-action is [x,m]=ι_R(x)•m, and M^L is
{m | ι_R(x)•m=0 for every x∈L}.
Let M′ be another left U-module in an independent carrier universe
and f:M→M′ a U-linear map.
The induced H^0 coefficient map is obtained from the zero-kernel
map through H^0≃ker(d^0) on both sides. -/
def leftCohomologyZeroCoefficientMap (f : M →ₗ[U] M') :
    (leftCoefficientCochainComplex R L M).homology 0 →ₗ[R]
      (leftCoefficientCochainComplex R L M').homology 0 :=
  (leftCohomologyZeroKernelEquiv R L M').symm.toLinearMap.comp
    ((leftCochainZeroCoefficientKernelMap R L f).comp
      (leftCohomologyZeroKernelEquiv R L M).toLinearMap)

/-- Let R:Type u be commutative, L:Type v an R-Lie algebra,
and M a left U=UEA_R(L)-module with carrier universe w.
Its restricted L-action is [x,m]=ι_R(x)•m, and M^L is
{m | ι_R(x)•m=0 for every x∈L}.
Let M′ be another left U-module in an independent carrier universe
and f:M→M′ a U-linear map.
The invariant equivalences satisfy
E_{M′} H^0(f)=f^{inv} E_M across the independent coefficient worlds. -/
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

/-- Let R be commutative, L an R-Lie algebra and X a left Lie module.
Represent X as a UEA_R(L)-module and restrict it back through the
generators. The representation/restriction unit identifies the resulting
invariant module with the maximal trivial Lie submodule X^L. -/
def representedCoefficientInvariantsEquiv (X : LieModuleCat.{w} R L) :
    leftCoefficientInvariants R L (LieModuleCat.UniversalEnveloping.representObj R L X) ≃ₗ[R]
      LieModule.maxTrivSubmodule R L X :=
  LinearEquiv.ofLinearMap
    (LieModule.maxTrivHom ((LieModuleCat.UniversalEnveloping.unitIso R L X).inv)).toLinearMap
    (LieModule.maxTrivHom ((LieModuleCat.UniversalEnveloping.unitIso R L X).hom)).toLinearMap
    (by apply LinearMap.ext; intro m; apply Subtype.ext; rfl)
    (by apply LinearMap.ext; intro m; apply Subtype.ext; rfl)

/-- Let R be commutative, L an R-Lie algebra and X any compatible
left Lie module. With its represented enveloping module Rep(X),
the R-linear comparison is H^0(L,Rep(X))≃X^L, preserving X's
coefficient carrier universe. -/
def coefficientCohomologyZeroLinearEquiv (X : LieModuleCat.{w} R L) :
    (leftCoefficientCochainComplex R L
      (LieModuleCat.UniversalEnveloping.representObj R L X)).homology 0 ≃ₗ[R]
        LieModule.maxTrivSubmodule R L X :=
  (leftCoefficientCohomologyZeroLinearEquiv R L
    (LieModuleCat.UniversalEnveloping.representObj R L X)).trans
      (representedCoefficientInvariantsEquiv R L X)

/-- For a compatible left Lie module X over an R-Lie algebra L,
with R commutative, the categorical comparison is
H^0(L,Rep(X))≅U^{max{u,v,w}}X^L in the cochain module category. -/
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

/-- Let R,S be commutative rings, L an R-Lie algebra and J an S-Lie
algebra. Put U_R=UEA_R(L), U_S=UEA_S(J). Let σ:R→S and
τ:U_R→U_S be ring maps with τ(algMap_R(r))=algMap_S(σ(r)).
Let M,N be left U_R,U_S-modules and g:Res_τ(N)→M U_R-linear.
The coefficient function g:N→M is R-linear after restricting
N along σ. This follows from the scalar equation for τ. -/
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

/-- Let R,S be commutative rings, L an R-Lie algebra and J an S-Lie
algebra. Put U_R=UEA_R(L), U_S=UEA_S(J). Let σ:R→S and
τ:U_R→U_S be ring maps with τ(algMap_R(r))=algMap_S(σ(r)).
Let M,N be left U_R,U_S-modules and g:Res_τ(N)→M U_R-linear.
Restriction on zero-cochains sends a:Λ_S^0J→N to
z↦e_R(z)•g(a(1_J)):Λ_R^0L→M, where e_R:Λ_R^0L≃R.
The source cochains carry their R-action through σ. -/
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

/-- Let R,S be commutative rings, L an R-Lie algebra and J an S-Lie
algebra. Put U_R=UEA_R(L), U_S=UEA_S(J). Let σ:R→S and
τ:U_R→U_S be ring maps with τ(algMap_R(r))=algMap_S(σ(r)).
Let M,N be left U_R,U_S-modules and g:Res_τ(N)→M U_R-linear.
Let φ:L→J be a homomorphism of the underlying ℤ-Lie algebras,
with τ(ι_R(x))=ι_S(φ(x)) for every x∈L.
The zero-cochain restriction map sends ker(d_J^0) to ker(d_L^0).
The generator equation ensures ι_R(x)g(n)=g(ι_S(φ(x))n),
so a J-invariant coefficient value remains L-invariant. -/
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
/-- Let R,S be commutative rings, L an R-Lie algebra and J an S-Lie
algebra. Put U_R=UEA_R(L), U_S=UEA_S(J). Let σ:R→S and
τ:U_R→U_S be ring maps with τ(algMap_R(r))=algMap_S(σ(r)).
Let M,N be left U_R,U_S-modules and g:Res_τ(N)→M U_R-linear.
Let φ:L→J be a homomorphism of the underlying ℤ-Lie algebras,
with τ(ι_R(x))=ι_S(φ(x)) for every x∈L.
Restriction gives an R-linear map N^J→M^L, n↦g(n),
with the R-action on N^J induced by σ. -/
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
/-- Let R,S be commutative rings, L an R-Lie algebra and J an S-Lie
algebra. Put U_R=UEA_R(L), U_S=UEA_S(J). Let σ:R→S and
τ:U_R→U_S be ring maps with τ(algMap_R(r))=algMap_S(σ(r)).
Let M,N be left U_R,U_S-modules and g:Res_τ(N)→M U_R-linear.
Let φ:L→J be a homomorphism of the underlying ℤ-Lie algebras,
with τ(ι_R(x))=ι_S(φ(x)) for every x∈L.
Empty-wedge kernel evaluation commutes with restriction:
E_R(K^{res}(a))=I^{res}(E_S(a)) for every zero cocycle a on J. -/
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

/-- Let R,S be commutative rings, L an R-Lie algebra and J an S-Lie
algebra. Put U_R=UEA_R(L), U_S=UEA_S(J). Let σ:R→S and
τ:U_R→U_S be ring maps with τ(algMap_R(r))=algMap_S(σ(r)).
Let M,N be left U_R,U_S-modules and g:Res_τ(N)→M U_R-linear.
Let φ:L→J be a homomorphism of the underlying ℤ-Lie algebras,
with τ(ι_R(x))=ι_S(φ(x)) for every x∈L.
The zero-kernel restriction induces the R-linear map
H^0(J,N)→H^0(L,M), with the source scalar action restricted
from S through σ. -/
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

/-- Let R,S be commutative rings, L an R-Lie algebra and J an S-Lie
algebra. Put U_R=UEA_R(L), U_S=UEA_S(J). Let σ:R→S and
τ:U_R→U_S be ring maps with τ(algMap_R(r))=algMap_S(σ(r)).
Let M,N be left U_R,U_S-modules and g:Res_τ(N)→M U_R-linear.
Let φ:L→J be a homomorphism of the underlying ℤ-Lie algebras,
with τ(ι_R(x))=ι_S(φ(x)) for every x∈L.
The H^0-to-invariants equivalences satisfy
E_R H^{0,res}=I^{res} E_S.
This is the naturality square for the underlying ring/Lie restriction. -/
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
