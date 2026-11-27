/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-
Modifications copyright (c) 2026 Meta Platforms, Inc. and affiliates.
-/
/-
Ported from TauCetiProject/TauCeti at
62bbc0596dc3539d488232e4e924a338548ea0a9:
TauCeti/RingTheory/CyclicCohomology/Cohomology.lean
Public source: https://github.com/TauCetiProject/TauCeti
The original contributors' copyright, author and Apache License 2.0
notice is retained above. Modification notice: use the explicitly
listed MathlibExt ports for this complete SBI dependency closure;
retain the mathematical declarations and original names. Identity-scalar
multilinear maps and endomorphism-application lemmas use the pinned
Mathlib API; the finite-coordinate port keeps only its four needed lemmas.
-/
module

public import MathlibExt.RingTheory.CyclicCochains
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import MathlibExt.Algebra.Homology.CyclicModuleHomology

/-!
# Cyclic cohomology

The cyclic cochains `C_λⁿ(A; M)` of an algebra `A`, the `M`-valued multilinear maps `φ` in
`n + 1` arguments with `φ(aₙ, a₀, …, aₙ₋₁) = (-1)ⁿ φ(a₀, …, aₙ)`, form a subcomplex of the
Hochschild cochains. This file assembles them into Connes' cyclic cochain complex
`cyclicCochainComplex R A M`, a cochain complex of `R`-modules indexed by `ℕ`, and defines the
cyclic cohomology `HCⁿ(A; M)` of a unital algebra as its categorical cohomology. This is Connes'
definition by cyclic cochains; over a ring containing `ℚ` it agrees with the cohomology of the
cyclic bicomplex (`TauCeti.RingTheory.CyclicCohomology.Bicomplex`).

The cyclic cocycles and coboundaries are also described concretely, as submodules of the cyclic
cochains, and `cyclicCohomology.mk` sends a cocycle to its class: it is surjective, and its kernel
consists exactly of the coboundaries, so linear maps out of cyclic cohomology are described by
`cyclicCohomology.desc`. In degree zero there are no coboundaries and the cocycles are
the traces, so `HC⁰(A; M)` is the module of `M`-valued traces on `A`.

A homomorphism of nonunital algebras `f : A →ₙₐ[R] B` pulls cyclic cochains back along `f`,
giving a cochain map `cyclicCochainComplex R B M ⟶ cyclicCochainComplex R A M` and a map on cyclic
cohomology, contravariantly functorial in `f`. The homomorphism is not required to preserve units,
since the algebra maps from `A` to the differential graded algebras of cycles need not.

The concrete cocycles and coboundaries are defined for nonassociative, nonunital semirings
when the `R`-action on `M` commutes with itself. Associativity is required to show that every
coboundary is a cocycle. A cyclic coboundary vanishes on tuples of cyclically adjacent
quasi-inverse entries, without an associativity assumption. The categorical complex and cohomology
use a commutative ring.

The cochain complex is defined for nonunital algebras. Its cohomology is only named cyclic
cohomology for unital `A`: the cyclic cohomology of a nonunital algebra is instead defined through
its forced unitization, and in general differs from the cohomology of this complex.

## Main definitions

* `TauCeti.cyclicCochainComplex`: the cyclic cochain complex.
* `TauCeti.cyclicCocycles`, `TauCeti.cyclicCoboundaries`: cyclic cocycles and coboundaries.
* `TauCeti.cyclicCohomology`: the cyclic cohomology `HCⁿ(A; M)`.
* `TauCeti.cyclicCohomology.mk`: the class of a cyclic cocycle.
* `TauCeti.cyclicCohomology.desc`: the linear map out of cyclic cohomology induced by a linear map
  on cyclic cocycles vanishing on cyclic coboundaries.
* `TauCeti.cyclicCochainComplexMap`, `TauCeti.cyclicCohomology.map`: pullback along a
  homomorphism of nonunital algebras, induced by `TauCeti.cyclicCochainsMap`.

## Main results

* `TauCeti.apply_eq_zero_of_mem_cyclicCoboundaries_of_add_add_mul_eq_zero`: a cyclic coboundary
  vanishes on a tuple whose cyclically adjacent entries are quasi-inverse.
* `TauCeti.cyclicCohomology.mk_surjective`, `TauCeti.cyclicCohomology.mk_eq_zero_iff`: cyclic
  cohomology is the quotient of cyclic cocycles by cyclic coboundaries.
* `TauCeti.cyclicCohomology.zeroEquiv`, `TauCeti.mem_cyclicCocycles_zero_iff`: `HC⁰(A; M)` is the
  module of `M`-valued traces on `A`.
* `TauCeti.cyclicCohomology.map_id`, `TauCeti.cyclicCohomology.map_comp`: functoriality.

## References

* A. Connes, *Noncommutative Geometry*, Chapter III, §1.
* J.-L. Loday, *Cyclic Homology*, §2.1.

The concrete description of cohomology classes through `mk` follows the pattern of the de Rham
cohomology file `TauCeti.Geometry.Manifold.DeRham.Basic`.
-/

public section

noncomputable section

open CategoryTheory

namespace TauCeti

universe u

section Cocycles

variable (R : Type*) (A : Type u) (M : Type*) [Semiring R] [NonUnitalNonAssocSemiring A]
  [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]
  [SMulCommClass R R M]

/-- The cyclic `n`-cocycles: the cyclic cochains annihilated by the Hochschild coboundary. -/
def cyclicCocycles (n : ℕ) : Submodule R (cyclicCochains R A M n) :=
  LinearMap.ker (cyclicHochschildCoboundary R A M n)

/-- A cyclic cochain is a cocycle exactly when its Hochschild coboundary vanishes. -/
@[simp]
theorem mem_cyclicCocycles_iff {n : ℕ} {φ : cyclicCochains R A M n} :
    φ ∈ cyclicCocycles R A M n ↔
      hochschildCoboundary R A M n (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A)
          M) = 0 := by
  rw [cyclicCocycles, LinearMap.mem_ker, ← Subtype.coe_inj, coe_cyclicHochschildCoboundary_apply,
    ZeroMemClass.coe_zero]

/-- The cyclic `n`-coboundaries: zero in degree zero, and the image of the Hochschild coboundary
of cyclic `n`-cochains in degree `n + 1`. -/
def cyclicCoboundaries : (n : ℕ) → Submodule R (cyclicCochains R A M n)
  | 0 => ⊥
  | n + 1 => LinearMap.range (cyclicHochschildCoboundary R A M n)

/-- There are no nonzero cyclic coboundaries in degree zero. -/
@[simp]
theorem cyclicCoboundaries_zero : cyclicCoboundaries R A M 0 = ⊥ := (rfl)

/-- In positive degree the cyclic coboundaries are the image of the Hochschild coboundary. -/
theorem cyclicCoboundaries_succ (n : ℕ) :
    cyclicCoboundaries R A M (n + 1) = LinearMap.range (cyclicHochschildCoboundary R A M n) :=
  (rfl)

/-- A cyclic `(n + 1)`-cochain is a coboundary exactly when it is the Hochschild coboundary of a
cyclic `n`-cochain. -/
@[simp]
theorem mem_cyclicCoboundaries_succ_iff {n : ℕ} {φ : cyclicCochains R A M (n + 1)} :
    φ ∈ cyclicCoboundaries R A M (n + 1) ↔
      ∃ ψ : cyclicCochains R A M n, cyclicHochschildCoboundary R A M n ψ = φ := by
  rw [cyclicCoboundaries_succ, LinearMap.mem_range]

variable {R A M} in
/-- A cyclic coboundary vanishes on a tuple whose cyclically adjacent entries `xᵢ`, `xᵢ₊₁` are
quasi-inverse, `xᵢ₊₁ + xᵢ + xᵢxᵢ₊₁ = 0`. -/
theorem apply_eq_zero_of_mem_cyclicCoboundaries_of_add_add_mul_eq_zero {n : ℕ}
    {φ : cyclicCochains R A M n} (hφ : φ ∈ cyclicCoboundaries R A M n) {x : Fin (n + 1) → A}
    (hx : ∀ i, x (finRotate (n + 1) i) + x i + x i * x (finRotate (n + 1) i) = 0) :
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M) x = 0 := by
  cases n with
  | zero =>
    rw [cyclicCoboundaries_zero, Submodule.mem_bot] at hφ
    rw [hφ, ZeroMemClass.coe_zero, zero_apply]
  | succ n =>
    obtain ⟨ψ, rfl⟩ := (mem_cyclicCoboundaries_succ_iff _ _ _).1 hφ
    rw [coe_cyclicHochschildCoboundary_apply]
    exact hochschildCoboundary_apply_eq_zero_of_add_add_mul_eq_zero ψ.2 hx

/-- A cyclic `0`-cochain is a cocycle exactly when it is a trace. -/
theorem mem_cyclicCocycles_zero_iff {φ : cyclicCochains R A M 0} :
    φ ∈ cyclicCocycles R A M 0 ↔
      ∀ x y : A, (φ : MultilinearMap (RingHom.id R) (fun _ : Fin 1 ↦ A) M) (fun _ ↦ x * y) =
        (φ : MultilinearMap (RingHom.id R) (fun _ : Fin 1 ↦ A) M) (fun _ ↦ y * x) := by
  rw [mem_cyclicCocycles_iff, hochschildCoboundary_zero_eq_zero_iff]

variable {R A M} {B : Type u} [NonUnitalNonAssocSemiring B] [Module R B] [IsScalarTower R B B]
  [SMulCommClass R B B]

/-- The pullback of a cyclic cocycle is a cyclic cocycle. -/
theorem cyclicCochainsMap_mem_cyclicCocycles (f : A →ₙₐ[R] B) {n : ℕ}
    {φ : cyclicCochains R B M n} (hφ : φ ∈ cyclicCocycles R B M n) :
    cyclicCochainsMap M (f : A →ₗ[R] B) n φ ∈ cyclicCocycles R A M n := by
  rw [cyclicCocycles, LinearMap.mem_ker, cyclicHochschildCoboundary_cyclicCochainsMap,
    LinearMap.mem_ker.1 hφ, map_zero]

end Cocycles

section AssociativeCocycles

variable (R : Type*) (A : Type u) (M : Type*) [Semiring R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]
  [SMulCommClass R R M]

/-- Every cyclic coboundary is a cyclic cocycle. -/
theorem cyclicCoboundaries_le_cyclicCocycles (n : ℕ) :
    cyclicCoboundaries R A M n ≤ cyclicCocycles R A M n := by
  cases n with
  | zero => simp
  | succ n =>
    exact LinearMap.range_le_ker_iff.2
      (cyclicHochschildCoboundary_comp_cyclicHochschildCoboundary R A M)

end AssociativeCocycles

section Complex

variable (R : Type*) (A : Type u) (M : Type*) [CommRing R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]

/-- Connes' cyclic cochain complex `C_λ⁰ → C_λ¹ → ⋯`: in degree `n` the cyclic `M`-valued
`n`-cochains on `A`, with the Hochschild coboundary as differential. -/
def cyclicCochainComplex : CochainComplex (ModuleCat R) ℕ :=
  CochainComplex.of (fun n ↦ ModuleCat.of R (cyclicCochains R A M n))
    (fun n ↦ ModuleCat.ofHom (cyclicHochschildCoboundary R A M n))
    fun _ ↦ ModuleCat.hom_ext (cyclicHochschildCoboundary_comp_cyclicHochschildCoboundary R A M)

/-- The degree-`n` term of the cyclic cochain complex is the module of cyclic `n`-cochains. -/
def cyclicCochainComplexXIso (n : ℕ) :
    (cyclicCochainComplex R A M).X n ≅ ModuleCat.of R (cyclicCochains R A M n) :=
  Iso.refl _

/-- Under the identifications `cyclicCochainComplexXIso`, the differential of the cyclic cochain
complex is the Hochschild coboundary. -/
@[reassoc, elementwise]
theorem cyclicCochainComplex_d (n : ℕ) :
    (cyclicCochainComplex R A M).d n (n + 1) ≫ (cyclicCochainComplexXIso R A M (n + 1)).hom =
      (cyclicCochainComplexXIso R A M n).hom ≫
        ModuleCat.ofHom (cyclicHochschildCoboundary R A M n) := by
  simp [cyclicCochainComplex, cyclicCochainComplexXIso]

/-- A cyclic cochain is a cyclic cocycle exactly when the differential of the cyclic cochain
complex kills it. -/
theorem mem_cyclicCocycles_iff_complex (n : ℕ) (φ : cyclicCochains R A M n) :
    φ ∈ cyclicCocycles R A M n ↔
      (cyclicCochainComplex R A M).d n (n + 1)
        ((cyclicCochainComplexXIso R A M n).inv φ) = 0 := by
  rw [cyclicCocycles, LinearMap.mem_ker, (cyclicCochainComplex R A M).moduleCat_d_inv_eq_zero_iff
    (cyclicHochschildCoboundary R A M) (cyclicCochainComplex_d R A M)]

section Map

variable {R A M} {B C : Type u} [NonUnitalSemiring B] [Module R B] [IsScalarTower R B B]
  [SMulCommClass R B B] [NonUnitalSemiring C] [Module R C] [IsScalarTower R C C]
  [SMulCommClass R C C]

variable (M) in
/-- The cochain map between cyclic cochain complexes induced by a homomorphism of nonunital
algebras. -/
def cyclicCochainComplexMap (f : A →ₙₐ[R] B) :
    cyclicCochainComplex R B M ⟶ cyclicCochainComplex R A M where
  f n := ModuleCat.ofHom (cyclicCochainsMap M (f : A →ₗ[R] B) n)
  comm' := by
    rintro n _ rfl
    ext φ : 2
    simp only [cyclicCochainComplex, CochainComplex.of_d, ModuleCat.hom_comp, ModuleCat.hom_ofHom]
    exact cyclicHochschildCoboundary_cyclicCochainsMap f φ

/-- Under the identifications `cyclicCochainComplexXIso`, the induced cochain map is the pullback
of cyclic cochains. This holds by definition, the identifications being identities. -/
@[reassoc, elementwise]
theorem cyclicCochainComplexMap_f (f : A →ₙₐ[R] B) (n : ℕ) :
    (cyclicCochainComplexMap M f).f n ≫ (cyclicCochainComplexXIso R A M n).hom =
      (cyclicCochainComplexXIso R B M n).hom ≫
        ModuleCat.ofHom (cyclicCochainsMap M (f : A →ₗ[R] B) n) :=
  (rfl)

/-- The identity homomorphism induces the identity cochain map. -/
@[simp]
theorem cyclicCochainComplexMap_id :
    cyclicCochainComplexMap M (NonUnitalAlgHom.id R A) = 𝟙 (cyclicCochainComplex R A M) := by
  ext n : 1
  dsimp only [cyclicCochainComplexMap, HomologicalComplex.id_f]
  -- The identity homomorphism coerces to the identity linear map by definition.
  exact (congrArg ModuleCat.ofHom (cyclicCochainsMap_id M n)).trans ModuleCat.ofHom_id

/-- The induced cochain map is contravariantly functorial. -/
theorem cyclicCochainComplexMap_comp (f : A →ₙₐ[R] B) (g : B →ₙₐ[R] C) :
    cyclicCochainComplexMap M (g.comp f) =
      cyclicCochainComplexMap M g ≫ cyclicCochainComplexMap M f := by
  ext n : 1
  dsimp only [cyclicCochainComplexMap, HomologicalComplex.comp_f]
  -- The composite homomorphism coerces to the composite linear map by definition.
  exact (congrArg ModuleCat.ofHom
    (cyclicCochainsMap_comp M (f : A →ₗ[R] B) (g : B →ₗ[R] C) n)).trans (ModuleCat.ofHom_comp _ _)

end Map

end Complex

section Cohomology

variable (R : Type*) (A : Type u) (M : Type*) [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M]
  [Module R M]

/-- The cyclic cohomology `HCⁿ(A; M)` of a unital algebra `A` with coefficients in `M`, the
cohomology of the cyclic cochain complex. For `M = R` this is Connes' cyclic cohomology `HCⁿ(A)`,
defined by cyclic cochains: over a ground ring containing `ℚ` it agrees with the cohomology of
the cyclic bicomplex (`TauCeti.RingTheory.CyclicCohomology.Bicomplex`), and over other rings the
two can differ. -/
abbrev cyclicCohomology (n : ℕ) : ModuleCat R :=
  (cyclicCochainComplex R A M).homology n

private theorem mem_cyclicCoboundaries_iff_complex (n : ℕ) (φ : cyclicCochains R A M n) :
    φ ∈ cyclicCoboundaries R A M n ↔
      ∃ y : (cyclicCochainComplex R A M).X ((ComplexShape.up ℕ).prev n),
        (cyclicCochainComplex R A M).d ((ComplexShape.up ℕ).prev n) n y =
          (cyclicCochainComplexXIso R A M n).inv φ :=
  (cyclicCochainComplex R A M).moduleCat_mem_iff_exists_d_eq_inv (cyclicCoboundaries R A M)
    (cyclicHochschildCoboundary R A M) (cyclicCochainComplex_d R A M)
    (cyclicCoboundaries_zero R A M) (cyclicCoboundaries_succ R A M) n φ

private abbrev toCycles (n : ℕ) (φ : cyclicCocycles R A M n) :=
  (cyclicCochainComplex R A M).moduleCatCyclesMk ((cyclicCochainComplexXIso R A M n).inv φ.1)
    (n + 1) (CochainComplex.next ℕ n) ((mem_cyclicCocycles_iff_complex R A M n φ.1).1 φ.2)

private theorem iCycles_toCycles (n : ℕ) (φ : cyclicCocycles R A M n) :
    (cyclicCochainComplex R A M).iCycles n (toCycles R A M n φ) = φ.1 :=
  (cyclicCochainComplex R A M).iCycles_moduleCatCyclesMk _ _ _ _ _

namespace cyclicCohomology

/-- The cyclic cohomology class of a cyclic cocycle. -/
def mk (n : ℕ) : cyclicCocycles R A M n →ₗ[R] cyclicCohomology R A M n :=
  (cyclicCochainComplex R A M).moduleCatCohomologyClassOfIso
    (fun n ↦ cyclicCochains R A M n) (cyclicCocycles R A M)
    (cyclicCochainComplexXIso R A M) (mem_cyclicCocycles_iff_complex R A M) n

/-- The class of a cyclic cocycle is the homology class of the corresponding cycle. -/
private theorem mk_apply (n : ℕ) (φ : cyclicCocycles R A M n) :
    mk R A M n φ = (cyclicCochainComplex R A M).homologyπ n (toCycles R A M n φ) :=
  (cyclicCochainComplex R A M).moduleCatCohomologyClassOfIso_apply
    (fun n ↦ cyclicCochains R A M n) (cyclicCocycles R A M)
    (cyclicCochainComplexXIso R A M) (mem_cyclicCocycles_iff_complex R A M) n φ

/-- The class of a cyclic cocycle `φ` is the homology class of any cycle of the cyclic cochain
complex whose underlying cochain is `φ`. -/
theorem mk_eq_homologyπ {n : ℕ} (φ : cyclicCocycles R A M n)
    (z : (cyclicCochainComplex R A M).cycles n)
    (hz : (cyclicCochainComplexXIso R A M n).hom ((cyclicCochainComplex R A M).iCycles n z) = φ) :
    mk R A M n φ = (cyclicCochainComplex R A M).homologyπ n z :=
  (cyclicCochainComplex R A M).moduleCatCohomologyClassOfIso_eq_homologyπ
    (fun n ↦ cyclicCochains R A M n) (cyclicCocycles R A M)
    (cyclicCochainComplexXIso R A M) (mem_cyclicCocycles_iff_complex R A M) φ z hz

/-- Every cyclic cohomology class is the class of a cyclic cocycle. -/
theorem mk_surjective (n : ℕ) : Function.Surjective (mk R A M n) := by
  exact (cyclicCochainComplex R A M).moduleCatCohomologyClassOfIso_surjective
    (fun n ↦ cyclicCochains R A M n) (cyclicCocycles R A M)
    (cyclicCochainComplexXIso R A M) (mem_cyclicCocycles_iff_complex R A M) n

/-- A cyclic cocycle has zero cohomology class exactly when it is a cyclic coboundary. -/
@[simp]
theorem mk_eq_zero_iff (n : ℕ) (φ : cyclicCocycles R A M n) :
    mk R A M n φ = 0 ↔ (φ : cyclicCochains R A M n) ∈ cyclicCoboundaries R A M n := by
  exact (cyclicCochainComplex R A M).moduleCatCohomologyClassOfIso_eq_zero_iff
    (fun n ↦ cyclicCochains R A M n) (cyclicCocycles R A M) (cyclicCoboundaries R A M)
    (cyclicCochainComplexXIso R A M) (mem_cyclicCocycles_iff_complex R A M)
    (mem_cyclicCoboundaries_iff_complex R A M) n φ

/-- Two cyclic cocycles have the same class exactly when they differ by a cyclic coboundary. -/
theorem mk_eq_mk_iff (n : ℕ) (φ ψ : cyclicCocycles R A M n) :
    mk R A M n φ = mk R A M n ψ ↔
      (φ : cyclicCochains R A M n) - ψ ∈ cyclicCoboundaries R A M n := by
  exact (cyclicCochainComplex R A M).moduleCatCohomologyClassOfIso_eq_iff
    (fun n ↦ cyclicCochains R A M n) (cyclicCocycles R A M) (cyclicCoboundaries R A M)
    (cyclicCochainComplexXIso R A M) (mem_cyclicCocycles_iff_complex R A M)
    (mem_cyclicCoboundaries_iff_complex R A M) n φ ψ

/-- In degree zero the class map is injective: there are no nonzero cyclic coboundaries. -/
theorem mk_zero_injective : Function.Injective (mk R A M 0) := by
  refine (injective_iff_map_eq_zero _).2 fun φ hφ ↦ ?_
  rw [mk_eq_zero_iff, cyclicCoboundaries_zero, Submodule.mem_bot] at hφ
  exact Subtype.ext hφ

/-- `HC⁰(A; M)` is the module of cyclic `0`-cocycles. Every `0`-cochain is cyclic
(`cyclicCochains_zero`) and the `0`-cocycles are the traces (`mem_cyclicCocycles_zero_iff`), so this
identifies `HC⁰(A; M)` with the module of `M`-valued traces on `A`. -/
def zeroEquiv : cyclicCocycles R A M 0 ≃ₗ[R] cyclicCohomology R A M 0 :=
  LinearEquiv.ofBijective (mk R A M 0) ⟨mk_zero_injective R A M, mk_surjective R A M 0⟩

/-- The equivalence `zeroEquiv` sends a cyclic `0`-cocycle to its class. -/
@[simp]
theorem zeroEquiv_apply (φ : cyclicCocycles R A M 0) : zeroEquiv R A M φ = mk R A M 0 φ :=
  (rfl)

section Desc

variable {R A M} {N : Type*} [AddCommGroup N] [Module R N]

/-- Two linear maps out of cyclic cohomology agree once they agree on classes of cocycles. -/
@[ext]
theorem linearMap_ext {n : ℕ} {f g : cyclicCohomology R A M n →ₗ[R] N}
    (h : f ∘ₗ mk R A M n = g ∘ₗ mk R A M n) : f = g :=
  LinearMap.ext fun z ↦ by
    obtain ⟨φ, rfl⟩ := mk_surjective R A M n z
    exact LinearMap.congr_fun h φ

/-- A linear map on cyclic cocycles that vanishes on cyclic coboundaries descends to cyclic
cohomology. -/
def desc (n : ℕ) (f : cyclicCocycles R A M n →ₗ[R] N)
    (hf : ∀ φ : cyclicCocycles R A M n,
      (φ : cyclicCochains R A M n) ∈ cyclicCoboundaries R A M n → f φ = 0) :
    cyclicCohomology R A M n →ₗ[R] N :=
  (mk R A M n).liftOfSurjective (mk_surjective R A M n)
    ⟨f, fun φ hφ ↦
      LinearMap.mem_ker.2 (hf φ ((mk_eq_zero_iff R A M n φ).1 (LinearMap.mem_ker.1 hφ)))⟩

/-- The descended map sends the class of a cocycle to the value of the original map. -/
@[simp]
theorem desc_mk (n : ℕ) (f : cyclicCocycles R A M n →ₗ[R] N)
    (hf : ∀ φ : cyclicCocycles R A M n,
      (φ : cyclicCochains R A M n) ∈ cyclicCoboundaries R A M n → f φ = 0)
    (φ : cyclicCocycles R A M n) :
    desc n f hf (mk R A M n φ) = f φ :=
  LinearMap.equivOfSurjective_apply _ _

/-- The descended map composed with the class map is the original map. -/
@[simp]
theorem desc_comp_mk (n : ℕ) (f : cyclicCocycles R A M n →ₗ[R] N)
    (hf : ∀ φ : cyclicCocycles R A M n,
      (φ : cyclicCochains R A M n) ∈ cyclicCoboundaries R A M n → f φ = 0) :
    desc n f hf ∘ₗ mk R A M n = f :=
  LinearMap.ext (desc_mk n f hf)

end Desc

section Map

variable {R A M} {B C : Type u} [Ring B] [Algebra R B] [Ring C] [Algebra R C]

variable (M) in
/-- The map on cyclic cohomology induced by a homomorphism of nonunital algebras between unital
algebras; the homomorphism need not preserve the unit. -/
def map (f : A →ₙₐ[R] B) (n : ℕ) : cyclicCohomology R B M n ⟶ cyclicCohomology R A M n :=
  HomologicalComplex.homologyMap (cyclicCochainComplexMap M f) n

/-- The induced map sends the class of a cocycle to the class of its pullback. -/
@[simp]
theorem map_mk (f : A →ₙₐ[R] B) {n : ℕ} (φ : cyclicCocycles R B M n) :
    map M f n (mk R B M n φ) =
      mk R A M n
        ⟨cyclicCochainsMap M (f : A →ₗ[R] B) n φ, cyclicCochainsMap_mem_cyclicCocycles f φ.2⟩ := by
  rw [map, mk_apply, mk_apply, ← ConcreteCategory.comp_apply,
    HomologicalComplex.homologyπ_naturality, ConcreteCategory.comp_apply]
  congr 1
  apply (cyclicCochainComplex R A M).moduleCat_iCycles_injective n
  rw [HomologicalComplex.moduleCat_iCycles_cyclesMap_apply, iCycles_toCycles, iCycles_toCycles]
  -- Both sides are the pullback of `φ`, as `cyclicCochainComplexXIso` is the identity.
  rfl

/-- The identity homomorphism induces the identity on cyclic cohomology. -/
@[simp]
theorem map_id (n : ℕ) : map M (NonUnitalAlgHom.id R A) n = 𝟙 _ := by
  rw [map, cyclicCochainComplexMap_id, HomologicalComplex.homologyMap_id]

/-- Cyclic cohomology is contravariantly functorial. -/
theorem map_comp (f : A →ₙₐ[R] B) (g : B →ₙₐ[R] C) (n : ℕ) :
    map M (g.comp f) n = map M g n ≫ map M f n := by
  rw [map, map, map, cyclicCochainComplexMap_comp, HomologicalComplex.homologyMap_comp]

end Map

end cyclicCohomology

end Cohomology

end TauCeti
