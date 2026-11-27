/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Module.Lattice.Full
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.Length
public import MathlibExt.RingTheory.DedekindDomain.DiscriminantTower
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct

/-!
# Mass and local factors of definite Hermitian lattices

We work over a fixed totally imaginary quadratic extension of a totally real number field.
The Hermitian pairing is linear on the left and conjugate-linear on the right. The lattice
need not have a basis over the ring of integers. Neither finiteness of the genus class set
nor existence of the density limit is asserted here.

Source: Markus Kirschmer, *Definite quadratic and hermitian forms with small class number*,
RWTH Aachen University, 2016, Definitions 2.1.1, 2.1.2, 2.2.2, 2.3.3,
2.3.5, 2.4.2, 4.2.1, 4.2.2 and 4.2.6.

The completion at a nonzero base prime `p` is scalar extension from the ring of integers
of `K` to `AdicCompletion p.asIdeal (𝓞 K)`. In particular, the completed dual is
obtained by applying this construction to the *global* integral dual. The completed dual
quotient is taken after this base change. No decomposition into primes of `E` or
identification with an independently defined local polar lattice is used.
-/

public section

noncomputable section

open scoped NumberField TensorProduct BigOperators nonZeroDivisors Topology
open NumberField TensorProduct

namespace HermitianLattice

variable {K E V : Type*} [Field K] [NumberField K] [IsTotallyReal K]
  [Field E] [NumberField E] [IsTotallyComplex E] [Algebra K E] [Algebra.IsQuadraticExtension K E]

-- Use Mathlib's CM conjugation on the canonically real subfield of `E`.
set_option quotPrecheck false in
local notation "cmConj[" K ", " E "]" =>
  (letI := IsCMField.ofCMExtension K E; (IsCMField.complexConj E).toRingEquiv)

omit [NumberField K] in
private theorem conjugation_algebraMap (x : K) :
    cmConj[K, E] (algebraMap K E x) = algebraMap K E x := by
  let := IsCMField.ofCMExtension K E
  change IsCMField.complexConj E (algebraMap K E x) = algebraMap K E x
  simpa only [CMExtension.equivMaximalRealSubfield_apply]
    using IsCMField.complexConj_apply_eq_self E (CMExtension.equivMaximalRealSubfield K E x)

variable (K E V) in
/-- A Hermitian form of positive rank, positive at every real embedding of the base field. -/
structure DefiniteForm [AddCommGroup V] [Module E V] [Module.Finite E V] where
  /-- The pairing, linear in its first argument and conjugate-linear in its second. -/
  pairing : V →ₗ[E] V →ₛₗ[(cmConj[K, E]).toRingHom] E
  /-- Interchanging the two entries conjugates the value. -/
  hermitian : ∀ x y, pairing y x = cmConj[K, E] (pairing x y)
  /-- The Hermitian rank is the dimension over `E`, not the extension degree `[E : K]`. -/
  rank_pos : 0 < Module.finrank E V
  /-- Each nonzero diagonal value comes from a positive element at every real embedding of `K`. -/
  positive : ∀ (σ : K →+* ℝ) {x : V}, x ≠ 0 →
    ∃ a : K, algebraMap K E a = pairing x x ∧ 0 < σ a

variable [AddCommGroup V] [Module E V] [Module.Finite E V]
  [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]

variable (E V) in
/-- A finitely generated ring-of-integers submodule spanning the Hermitian space. -/
abbrev FullLattice := { L : Submodule (𝓞 E) V // L.IsFullLattice E }

variable (h : DefiniteForm K E V)

/-- The unitary group of the ambient Hermitian form. -/
@[expose] def unitaryGroup : Subgroup (V ≃ₗ[E] V) where
  carrier := { g | ∀ x y, h.pairing (g x) (g y) = h.pairing x y }
  one_mem' := fun _ _ ↦ rfl
  mul_mem' := fun hg hk x y ↦ (hg _ _).trans (hk _ _)
  inv_mem' := by
    intro g hg x y
    change h.pairing (g.symm x) (g.symm y) = h.pairing x y
    simpa only [LinearEquiv.apply_symm_apply] using (hg (g.symm x) (g.symm y)).symm

/-- The unitary group acts by taking the image of a submodule. -/
instance : MulAction (unitaryGroup h) (Submodule (𝓞 E) V) where
  smul g L := L.map (g.1.toLinearMap.restrictScalars (𝓞 E))
  one_smul L := Submodule.map_id L
  mul_smul g k L := by
    change L.map ((↑(g * k) : V ≃ₗ[E] V).toLinearMap.restrictScalars (𝓞 E)) =
      (L.map (k.1.toLinearMap.restrictScalars (𝓞 E))).map
        (g.1.toLinearMap.restrictScalars (𝓞 E))
    rw [← Submodule.map_comp]
    rfl

/-- The integral dual $L^\#$ consists of the vectors whose pairing with every vector of
$L$ lies in the ring of integers of $E$. It is a submodule over the ring of integers;
no choice of an integral basis is used. -/
@[expose] def dual (L : FullLattice E V) : Submodule (𝓞 E) V where
  carrier := { x | ∀ y : L.1, IsIntegral ℤ (h.pairing x y) }
  zero_mem' := fun y ↦ by
    change IsIntegral ℤ (h.pairing 0 y)
    rw [map_zero, LinearMap.zero_apply]
    exact isIntegral_zero
  add_mem' := fun {x y} hx hy z ↦ by
    change IsIntegral ℤ (h.pairing (x + y) z)
    rw [h.pairing.map_add₂]
    exact (hx z).add (hy z)
  smul_mem' := fun a x hx y ↦ by
    rw [← algebraMap_smul E a x, LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul]
    exact a.isIntegral_coe.mul (hx y)

/-- Integrality means that the lattice is contained in its integral dual. -/
abbrev IsIntegralLattice (L : FullLattice E V) : Prop := L.1 ≤ dual h L

/-- A lattice is unimodular if it equals its integral dual. -/
@[expose] def IsUnimodular (L : FullLattice E V) : Prop := L.1 = dual h L

local notation "𝒜[" p ", " K "]" =>
  AdicCompletion (IsDedekindDomain.HeightOneSpectrum.asIdeal p) (𝓞 K)
local notation "𝒬[" p ", " K ", " n "]" => (𝓞 K) ⧸ IsDedekindDomain.HeightOneSpectrum.asIdeal p ^ n

section Local

variable [Module (𝓞 K) V] [IsScalarTower (𝓞 K) (𝓞 E) V] [IsScalarTower (𝓞 K) E V]

private def completionInclusion (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (M : Submodule (𝓞 E) V) : (𝒜[p, K] ⊗[𝓞 K] M) →ₗ[𝒜[p, K]] (𝒜[p, K] ⊗[𝓞 K] V) :=
  TensorProduct.AlgebraTensorModule.lTensor 𝒜[p, K] 𝒜[p, K] (M.subtype.restrictScalars (𝓞 K))

omit [IsTotallyReal K] [NumberField E] [IsTotallyComplex E] [Algebra.IsQuadraticExtension K E]
  [Module E V] [Module.Finite E V] [IsScalarTower (𝓞 E) E V] [IsScalarTower (𝓞 K) E V] in
private theorem completionInclusion_injective (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (M : Submodule (𝓞 E) V) : Function.Injective (completionInclusion (E := E) p M) :=
  Module.Flat.lTensor_preserves_injective_linearMap (M := 𝒜[p, K])
    (M.subtype.restrictScalars (𝓞 K)) M.injective_subtype

/-- A lattice is unimodular at $\mathfrak p$ if its completion and the completion of its
integral dual have the same image in the completed ambient vector space. The two maps are
injective by flatness of adic completion of a Noetherian ring. This local condition does not
assume global integrality. -/
def IsUnimodularAt (L : FullLattice E V) (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : Prop :=
  LinearMap.range (completionInclusion (E := E) p L.1) =
    LinearMap.range (completionInclusion (E := E) p (dual h L))

omit [NumberField K] [IsScalarTower (𝓞 K) E V] in
/-- Local unimodularity is equality of the ranges of the two scalar-extended inclusions into
the completed ambient space, for the lattice and its integral dual respectively. -/
theorem isUnimodularAt_iff (L : FullLattice E V)
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    IsUnimodularAt h L p ↔
      LinearMap.range (TensorProduct.AlgebraTensorModule.lTensor 𝒜[p, K] 𝒜[p, K]
        (L.1.subtype.restrictScalars (𝓞 K))) =
      LinearMap.range (TensorProduct.AlgebraTensorModule.lTensor 𝒜[p, K] 𝒜[p, K]
        ((dual h L).subtype.restrictScalars (𝓞 K))) := Iff.rfl

/-- The scalar action on the base change of an integer lattice. The action of a pure scalar
`a ⊗ z` multiplies the first tensor factor by `a` and acts by `z` on the second. -/
instance (A : Type*) [CommRing A] [Algebra (𝓞 K) A]
    (L : Submodule (𝓞 E) V) : Module ((A ⊗[𝓞 K] 𝓞 E)) (A ⊗[𝓞 K] L) :=
  Module.compHom _ ((LinearMap.tensorProductEnd (𝓞 K) A L).comp
    (Algebra.TensorProduct.map (.id A A) (Algebra.lsmul (𝓞 K) (𝓞 K) L))).toRingHom

private def restrictedPairing (L : FullLattice E V) : LinearMap.BilinMap (𝓞 K) L.1 E :=
  LinearMap.mk₂ (𝓞 K) (fun x y ↦ h.pairing x y)
    (fun x y z ↦ congrArg (fun f : V →ₛₗ[(cmConj[K, E]).toRingHom] E ↦ f z)
      (h.pairing.map_add (x : V) y))
    (fun a x y ↦ by
      change h.pairing (a • (x : V)) y = a • h.pairing x y
      rw [← algebraMap_smul E a (x : V), h.pairing.map_smul, LinearMap.smul_apply,
        algebraMap_smul])
    (fun x y z ↦ (h.pairing x).map_add (y : V) z)
    (fun a x y ↦ by
      change h.pairing x (a • (y : V)) = a • h.pairing x y
      rw [← algebraMap_smul E a (y : V), (h.pairing x).map_smulₛₗ]
      change cmConj[K, E] (algebraMap K E (a : K)) • h.pairing x y = a • h.pairing x y
      rw [conjugation_algebraMap]
      exact algebraMap_smul E a _)

omit [NumberField K] [NumberField E] [IsTotallyReal K] [IsTotallyComplex E]
  [Algebra.IsQuadraticExtension K E] in
private theorem integers_smul_coe (a : 𝓞 K) (z : 𝓞 E) : ((a • z : 𝓞 E) : E) = a • (z : E) := by
  rw [← algebraMap_smul (𝓞 E) a z, ← algebraMap_smul E a (z : E)]
  rfl

private def restrictedIntegralPairing (L : FullLattice E V) (hi : IsIntegralLattice h L) :
    LinearMap.BilinMap (𝓞 K) L.1 (𝓞 E) :=
  LinearMap.mk₂ (𝓞 K) (fun x y ↦ ⟨h.pairing x y, hi x.2 y⟩)
    (fun x y z ↦ RingOfIntegers.ext ((restrictedPairing h L).map_add₂ x y z))
    (fun a x y ↦ by
      apply RingOfIntegers.ext
      exact ((restrictedPairing h L).map_smul₂ a x y).trans
        (integers_smul_coe a ⟨h.pairing x y, hi x.2 y⟩).symm)
    (fun x y z ↦ RingOfIntegers.ext (((restrictedPairing h L) x).map_add y z))
    (fun a x y ↦ by
      apply RingOfIntegers.ext
      exact (((restrictedPairing h L) x).map_smul a y).trans
        (integers_smul_coe a ⟨h.pairing x y, hi x.2 y⟩).symm)

/-- The Hermitian pairing on a lattice after extension of scalars from the base ring of integers
to a commutative algebra `A`, with values in `A ⊗ E` over the base integers. On simple
tensors its value is `(a * b) ⊗ h(x,y)`. This does not require integrality. -/
def localPairing (A : Type*) [CommRing A] [Algebra (𝓞 K) A] (L : FullLattice E V) :
    LinearMap.BilinMap A (A ⊗[𝓞 K] L.1) (A ⊗[𝓞 K] E) :=
  (restrictedPairing h L).baseChange A

/-- For an integral lattice the base-changed pairing takes values in the base-changed ring of
integers. The same construction works over the completion and over its finite quotients. -/
def localIntegralPairing (A : Type*) [CommRing A] [Algebra (𝓞 K) A]
    (L : FullLattice E V) (hi : IsIntegralLattice h L) :
    LinearMap.BilinMap A (A ⊗[𝓞 K] L.1) ((A ⊗[𝓞 K] 𝓞 E)) :=
  (restrictedIntegralPairing h L hi).baseChange A

omit [NumberField K] in
/-- On simple tensors, the base-changed pairing is the product of the new scalar coefficients
tensored with the original Hermitian pairing. -/
theorem localPairing_tmul (A : Type*) [CommRing A] [Algebra (𝓞 K) A] (L : FullLattice E V)
    (a b : A) (x y : L.1) :
    localPairing h A L (a ⊗ₜ[𝓞 K] x) (b ⊗ₜ[𝓞 K] y) =
      (a * b) ⊗ₜ[𝓞 K] h.pairing x y := by
  simp [localPairing, restrictedPairing, LinearMap.BilinMap.baseChange_tmul]

omit [NumberField K] in
/-- On simple tensors, the base-changed integral pairing takes the same product of scalar
coefficients and tensors it with the original pairing viewed in the ring of integers. -/
theorem localIntegralPairing_tmul (A : Type*) [CommRing A] [Algebra (𝓞 K) A]
    (L : FullLattice E V) (hi : IsIntegralLattice h L) (a b : A) (x y : L.1) :
    localIntegralPairing h A L hi (a ⊗ₜ[𝓞 K] x) (b ⊗ₜ[𝓞 K] y) =
      TensorProduct.tmul (𝓞 K) (N := 𝓞 E) (a * b) ⟨h.pairing x y, hi x.2 y⟩ := by
  rw [localIntegralPairing, LinearMap.BilinMap.baseChange_tmul]
  rfl

/-- The genus consists of all full lattices in the fixed space that are isometric over the
completed scalar ring at every nonzero prime of the base. -/
@[expose] def genus (L : FullLattice E V) : Set (FullLattice E V) :=
  { M | ∀ p : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
    Nonempty { f : (𝒜[p, K] ⊗[𝓞 K] L.1) ≃ₗ[(𝒜[p, K] ⊗[𝓞 K] 𝓞 E)]
        (𝒜[p, K] ⊗[𝓞 K] M.1) //
      ∀ x y, localPairing h 𝒜[p, K] M (f x) (f y) =
        localPairing h 𝒜[p, K] L x y } }

/-- The global isometry classes represented in the genus: the quotient by unitary orbits. -/
@[expose] def GenusClasses (L : FullLattice E V) :=
  Quotient ((MulAction.orbitRel (unitaryGroup h) (Submodule (𝓞 E) V)).comap
    (fun M : genus h L ↦ M.1.1))

/-- The group of global isometries that carry a lattice onto itself. -/
@[expose] def stabilizer (L : FullLattice E V) : Subgroup (unitaryGroup h) :=
  MulAction.stabilizer _ L.1

/-- The weight of a genus class is the reciprocal order of the finite unitary stabilizer
of any representative. Transport in a unitary orbit conjugates the stabilizers, so the
weight is defined on the quotient, independently of representatives. -/
@[expose] def classWeight (L : FullLattice E V)
    (finiteStabilizers : ∀ M : genus h L, Finite (stabilizer h M.1)) (c : GenusClasses h L) : ℚ :=
  Quotient.lift (fun M : genus h L ↦
    letI := finiteStabilizers M
    letI := Fintype.ofFinite (stabilizer h M.1)
    (Fintype.card (stabilizer h M.1) : ℚ)⁻¹) (fun M N e ↦ by
      have e' : MulAction.orbitRel (unitaryGroup h) (Submodule (𝓞 E) V) M.1.1 N.1.1 := e
      let := finiteStabilizers M
      let := finiteStabilizers N
      let := Fintype.ofFinite (stabilizer h M.1)
      let := Fintype.ofFinite (stabilizer h N.1)
      have equiv : stabilizer h M.1 ≃* stabilizer h N.1 :=
        MulAction.stabilizerEquivStabilizerOfOrbitRel e'
      change ((Fintype.card (stabilizer h M.1) : ℚ)⁻¹) =
        ((Fintype.card (stabilizer h N.1) : ℚ)⁻¹)
      rw [Fintype.card_congr equiv.toEquiv]) c

private def massValue (L : FullLattice E V) (finiteClasses : Finite (GenusClasses h L))
    (finiteStabilizers : ∀ M : genus h L, Finite (stabilizer h M.1)) : ℚ := by
  letI := finiteClasses
  letI := Fintype.ofFinite (GenusClasses h L)
  exact ∑ c : GenusClasses h L, classWeight h L finiteStabilizers c

/-- At precision `N`, all algebra-linear pairing-preserving endomorphisms are counted. In
particular there is no invertibility condition, even when the reduced form is degenerate. -/
@[expose] def PreservingEnd (L : FullLattice E V) (hi : IsIntegralLattice h L)
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (N : ℕ) :=
  { f : Module.End ((𝒬[p, K, N] ⊗[𝓞 K] 𝓞 E)) (𝒬[p, K, N] ⊗[𝓞 K] L.1) //
    ∀ x y, localIntegralPairing h 𝒬[p, K, N] L hi (f x) (f y) =
      localIntegralPairing h 𝒬[p, K, N] L hi x y }

/-- At each finite precision there are finitely many pairing-preserving endomorphisms. -/
instance (L : FullLattice E V) (hi : IsIntegralLattice h L)
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (N : ℕ) : Finite (PreservingEnd h L hi p N) := by
  let : Module.Finite (𝓞 K) (𝓞 E) := Module.Finite.of_restrictScalars_finite ℤ (𝓞 K) (𝓞 E)
  let : Module.Finite (𝓞 E) L.1 := Module.Finite.of_fg L.2.fg
  let : Module.Finite (𝓞 K) L.1 := Module.Finite.trans (𝓞 E) L.1
  let : Finite (𝒬[p, K, N]) :=
    Ring.HasFiniteQuotients.finiteQuotient (pow_ne_zero _ p.ne_bot)
  let : Finite (𝒬[p, K, N] ⊗[𝓞 K] L.1) := Module.finite_of_finite (𝒬[p, K, N])
  exact Finite.of_injective (fun f x ↦ f.1 x) (fun _ _ e ↦ Subtype.ext (LinearMap.ext (congrFun e)))

/-- The number of preserving endomorphisms, divided by the absolute prime norm to the power
`N * m * m`, where `m` is the rank of the Hermitian space over `E`. -/
@[expose] def normalizedCount (L : FullLattice E V) (hi : IsIntegralLattice h L)
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (N : ℕ) : ℝ :=
  let m := Module.finrank E V
  letI := Fintype.ofFinite (PreservingEnd h L hi p N)
  (Fintype.card (PreservingEnd h L hi p N) : ℝ) / (p.asIdeal.absNorm : ℝ) ^ (N * m * m)

/-- The local density is a real number together with evidence that the normalized counts tend to
it. No existence of the limit is assumed. In the CM case the ambient unitary group is connected,
so the component factor in Kirschmer, Definition 4.2.2 is one. -/
abbrev LocalDensity (L : FullLattice E V) (hi : IsIntegralLattice h L)
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :=
  { β : ℝ // Filter.Tendsto (normalizedCount h L hi p) Filter.atTop (𝓝 β) }

local notation "latticeInDual[" h ", " L "]" =>
  Submodule.comap (Submodule.subtype (dual h L)) (Subtype.val L)

/-- The quotient of the completed global dual by the image of the completed integral lattice.
The submodule `L` in the global dual is pulled back along its subtype map before extending
scalars. For integral `L`, this pullback is isomorphic to `L` by
`Submodule.comapSubtypeEquivOfLe`. -/
abbrev CompletedDualQuotient (L : FullLattice E V) (_hi : IsIntegralLattice h L)
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :=
  (𝒜[p, K] ⊗[𝓞 K] dual h L) ⧸ LinearMap.range
    (TensorProduct.AlgebraTensorModule.lTensor 𝒜[p, K] 𝒜[p, K]
      ((latticeInDual[h, L]).subtype.restrictScalars (𝓞 K)))

end Local

/-- The three possible splitting behaviors of a nonzero prime in a quadratic extension. -/
private inductive PrimeType
  | split
  | inert
  | ramified
  deriving DecidableEq

variable (E) in
/-- Classify a base prime using the ramification index and inertia degree in the given CM field.
If neither is two then both are one and there are two primes above the base prime. -/
private def primeType (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : PrimeType :=
  if p.asIdeal.ramificationIdxIn (𝓞 E) = 2 then .ramified
  else if p.asIdeal.inertiaDegIn (𝓞 E) = 2 then .inert
  else .split

/-- Normalized reference point count for Hermitian rank `m` and residue size `q`.
The product runs over `j = 1, …, m` in the split and inert cases, and over
`j = 1, …, ⌊m/2⌋` in the ramified case. -/
private def referenceCoefficient (kind : PrimeType) (q m : ℕ) : ℝ :=
  match kind with
  | .split => ∏ j ∈ Finset.range m, (1 - ((q : ℝ) ^ (j + 1))⁻¹)
  | .inert => ∏ j ∈ Finset.range m, (1 - ((-(q : ℝ)) ^ (j + 1))⁻¹)
  | .ramified => ∏ j ∈ Finset.range (m / 2), (1 - ((q : ℝ) ^ (2 * (j + 1)))⁻¹)

/-- The relative-discriminant correction is nonzero only for a ramified prime in even rank. -/
private def discriminantCorrection (kind : PrimeType) (discriminantOrder : ℤ) (m : ℕ) : ℝ :=
  if kind = .ramified ∧ Even m then (discriminantOrder : ℝ) * (m : ℝ) / 2 else 0

/-- The exponent of the local norm: half the product of dual quotient length and Hermitian
rank, with the ramified even-rank discriminant correction added. -/
private def normExponent (kind : PrimeType) (discriminantOrder : ℤ) (m t : ℕ) : ℝ :=
  (t : ℝ) * (m : ℝ) / 2 + discriminantCorrection kind discriminantOrder m

section LocalFactor

variable [Module (𝓞 K) V] [IsScalarTower (𝓞 K) (𝓞 E) V] [IsScalarTower (𝓞 K) E V]

/-- **Mass and local factor evaluations.** For a definite Hermitian form `h` and a full lattice
`L`, `MassAndLocalFactors` bundles two functions:

- `mass` returns a rational number given finiteness of the global isometry classes in the genus
  of `L` and finiteness of the unitary stabilizer of every lattice in that genus.
- `localFactor` returns a real number given integrality of `L`, a nonzero prime `p` of the
  base ring of integers, finite length of the completed dual quotient over the completed base
  ring at `p`, and a real density together with a witness that the normalized counts converge
  to it and a proof that it is nonzero.

The field types do not establish these premises or constrain the returned values to particular
formulas. The function `massAndLocalFactors` supplies the mass and local factor formulas. -/
structure MassAndLocalFactors (L : FullLattice E V) where
  /-- The genus mass: sum the reciprocals of the finite unitary stabilizer orders over the
  finitely many global isometry classes in the genus. -/
  mass : (finiteClasses : Finite (GenusClasses h L)) →
    (finiteStabilizers : ∀ M : genus h L, Finite (stabilizer h M.1)) → ℚ
  /-- The local factor at a nonzero prime of the base. It requires integrality, finite length of
  the completed dual quotient, and a nonzero density supplied with its limit witness. -/
  localFactor : (hi : IsIntegralLattice h L) → (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) →
    (finiteLength : Module.length 𝒜[p, K] (CompletedDualQuotient h L hi p) ≠ ⊤) →
    (β : LocalDensity h L hi p) → (nonzero : β.1 ≠ 0) → ℝ

/-- **Mass and local factors of definite Hermitian lattices.** The `MassAndLocalFactors` record
provides two named evaluations. Its `mass` is the sum of reciprocal finite stabilizer orders
over the finite set of genus classes. Its `localFactor` for an integral lattice at a finite
prime is the corrected norm power times the split, inert, or ramified reference coefficient
divided by the density. The density is given by a limit of normalized counts of all
form-preserving endomorphisms, with no invertibility test. Mass finiteness, finite length of the
completed dual quotient, and existence of a nonzero density are premises for the respective
evaluations, not assertions of this definition.

Source: M. Kirschmer, *Definite quadratic and hermitian forms with small class number*, RWTH
Aachen University (2016), Definitions 4.2.1, 4.2.2 and 4.2.6.
-/
def massAndLocalFactors (L : FullLattice E V) : MassAndLocalFactors h L where
  mass := massValue h L
  localFactor hi p _finiteLength β _nonzero :=
    let q := p.asIdeal.absNorm
    let m := Module.finrank E V
    let t := (Module.length 𝒜[p, K] (CompletedDualQuotient h L hi p)).toNat
    let kind := primeType E p
    let d := Ideal.discriminantIdeal (𝓞 K) (𝓞 E)
    let dOrder := FractionalIdeal.count K p (d : FractionalIdeal (𝓞 K)⁰ K)
    (q : ℝ) ^ normExponent kind dOrder m t * referenceCoefficient kind q m / β.1

/-- Given finite genus classes and finite unitary stabilizers for every lattice in the genus,
the mass evaluation sums the class weights over those classes. -/
theorem massAndLocalFactors_mass (L : FullLattice E V)
    (finiteClasses : Finite (GenusClasses h L))
    (finiteStabilizers : ∀ M : genus h L, Finite (stabilizer h M.1)) :
    (massAndLocalFactors h L).mass finiteClasses finiteStabilizers =
      letI := finiteClasses
      letI := Fintype.ofFinite (GenusClasses h L)
      ∑ c : GenusClasses h L, classWeight h L finiteStabilizers c := by
  rfl

/-- For an integral lattice at a nonzero prime, given finite length of the completed dual
quotient and a supplied nonzero density, the local factor is the prime norm to the corrected
exponent, times the reference product for the splitting behavior, divided by the density.
The exponent starts at half the product of quotient length and Hermitian rank. In the
ramified even-rank case it adds half the product of rank and relative discriminant order.
The reference product runs from index one through the rank, with the negative norm as
base in the inert case; in the ramified case it uses only the even indices up to the rank. -/
theorem massAndLocalFactors_localFactor (L : FullLattice E V) (hi : IsIntegralLattice h L)
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (finiteLength : Module.length 𝒜[p, K] (CompletedDualQuotient h L hi p) ≠ ⊤)
    (β : LocalDensity h L hi p) (nonzero : β.1 ≠ 0) :
    (massAndLocalFactors h L).localFactor hi p finiteLength β nonzero =
      let q := p.asIdeal.absNorm
      let m := Module.finrank E V
      let t := (Module.length 𝒜[p, K] (CompletedDualQuotient h L hi p)).toNat
      let d := Ideal.discriminantIdeal (𝓞 K) (𝓞 E)
      let ord := FractionalIdeal.count K p (d : FractionalIdeal (𝓞 K)⁰ K)
      let correction : ℝ := if p.asIdeal.ramificationIdxIn (𝓞 E) = 2 ∧ Even m
        then (ord : ℝ) * (m : ℝ) / 2 else 0
      let coeff : ℝ := if p.asIdeal.ramificationIdxIn (𝓞 E) = 2
        then ∏ j ∈ Finset.range (m / 2), (1 - ((q : ℝ) ^ (2 * (j + 1)))⁻¹)
        else if p.asIdeal.inertiaDegIn (𝓞 E) = 2
          then ∏ j ∈ Finset.range m, (1 - ((-(q : ℝ)) ^ (j + 1))⁻¹)
          else ∏ j ∈ Finset.range m, (1 - ((q : ℝ) ^ (j + 1))⁻¹)
      (q : ℝ) ^ ((t : ℝ) * (m : ℝ) / 2 + correction) * coeff / β.1 := by
  by_cases hr : p.asIdeal.ramificationIdxIn (𝓞 E) = 2
  · simp [massAndLocalFactors, primeType, normExponent, discriminantCorrection,
      referenceCoefficient, hr]
  · by_cases hi' : p.asIdeal.inertiaDegIn (𝓞 E) = 2 <;>
      simp [massAndLocalFactors, primeType, normExponent, discriminantCorrection,
        referenceCoefficient, hr, hi']

end LocalFactor

end HermitianLattice
