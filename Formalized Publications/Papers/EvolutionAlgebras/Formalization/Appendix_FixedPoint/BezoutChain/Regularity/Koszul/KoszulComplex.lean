/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# The Koszul complex as a `HomologicalComplex` (cochain and chain forms)

For a commutative ring `R`, an `R`-module `M`, and a degree-one charge
`ξ : ⋀[R]^1 M`, this file builds the Koszul complex `K(ξ)` as a
`CochainComplex (ModuleCat R) ℕ` (hence a `HomologicalComplex` with
`ComplexShape.up ℕ`). For `M = Fin n → R` and `x : Fin n → R`, the charge
`ξ = ι R x` gives the usual Koszul complex `K(x₁, …, xₙ)` of a sequence
(`koszulComplexOfSequence`). Dually, for `φ : M →ₗ[R] R` the interior-product
differential gives the chain form `K(φ)` as a `ChainComplex (ModuleCat R) ℕ`
(with `ComplexShape.down ℕ`), including `koszulChainComplexOfSequence` for
sequences.

## Design decision: wedge differential (§§2–4) plus contraction differential (§5)

The wedge differential `d(z) = ξ * z` (left multiplication by the charge)
yields the cochain complex (`d : Kᵏ → Kᵏ⁺¹`). This is the standard
cohomologically-indexed Koszul complex (Matsumura, Commutative Ring Theory,
§16; Weibel, Homological Algebra, §4.5, dual form): `d² = 0` follows from
`ξ * ξ = 0` (`charge_sq_zero`, via `ExteriorAlgebra.ι_sq_zero`), and the
complex bundles into Mathlib's `HomologicalComplex` with the full homology
API available.

The chain (contraction) form `d : Kₖ₊₁ → Kₖ` (§5, milestone R1) uses interior
products from `CliffordAlgebra.contractLeft` at `Q = 0` (the exterior algebra
*is* the Clifford algebra at `Q = 0`, by abbrev): degree-lowering
(`koszulContract_mem`, via the spanning set `ιMulti_span_fixedDegree`) and
`d² = 0` (`koszulContract_comp`, via `contractLeft_contractLeft`) both come
from the Clifford API. The bottom map agrees with `koszulContractOne`
(`koszulContract_ι`).

## Milestones (scoped-plan step A2)

* (1) Graded exterior-power modules: `piece_mul_mem`, `mem_piece_zero_one`,
  `mem_piece_one_iff`, `mem_ι_piece_one`, `mem_ιMulti_piece`,
  `exteriorAlgebraBasis`. Proved.
* (2) Differential maps: `koszulD` (wedge) with `koszulD_apply`,
  `koszulCharge`, plus the degree-one contraction `koszulContractOne`.
  proved (general contraction in §5).
* (3) `d² = 0`: `charge_sq_zero`, `koszulD_comp_koszulD`. Proved.
* (4) `HomologicalComplex` bundling: `koszulComplex`, `koszulComplexOfSequence`.
  proved.
* (5) General contraction + chain complex (R1): `contractLeft_ιMulti_mem`,
  `koszulContract_mem`, `koszulContract`, `koszulContract_ι`,
  `koszulContract_comp`, `koszulChainComplex`,
  `koszulChainComplexOfSequence`. Proved.
* (6) Rank formula (R4): `exteriorPower_finrank_of_finrank_eq`,
  `exteriorPower_finrank_fin_fun` (via `exteriorPower.finrank_eq`, the
  per-degree basis underlying `exteriorAlgebraBasis`). Proved.

## remaining (next milestones after this foundation)

* (R2) Exactness: `IsRegular M [x, y]` implies exactness of `K(x, y)` at
  positive degrees (chain form from (5) now available as the vehicle).
* (R3) Homology objects `Hᵏ(K(ξ))` via `HomologicalComplex.homology` and their
  identification with `Tor` / annihilator statements.
* (R1) and (R4) are proved — see (5) and (6) above.

## References

Mathlib (all read-only):
* `LinearAlgebra/ExteriorAlgebra/Basic.lean`: `exteriorPower` (`⋀[R]^n M`),
  `ExteriorAlgebra.ι`, `ι_sq_zero`, `ιInv`, `ι_leftInverse`, `ιMulti`,
  `ιMulti_range`.
* `LinearAlgebra/ExteriorAlgebra/Grading.lean`: the `SetLike.GradedMonoid`
  instance on `fun i ↦ ⋀[R]^i M` (consumed via `SetLike.GradedMul.mul_mem`
  and `SetLike.one_mem_graded`).
* `LinearAlgebra/ExteriorAlgebra/Basis.lean`: `Module.Basis.ExteriorAlgebra`.
* `LinearAlgebra/ExteriorPower/Basis.lean`: `Module.Basis.exteriorPower`,
  `exteriorPower.finrank_eq` (the R4 rank formula).
* `LinearAlgebra/CliffordAlgebra/Contraction.lean`: `contractLeft`,
  `contractLeft_ι_mul`, `contractLeft_contractLeft`, `contractLeft_ι`,
  `contractLeft_one` (the interior-product API behind §5, used at
  `Q = (0 : QuadraticForm R M)`).
* `LinearAlgebra/StdBasis.lean`: `Pi.basisFun` (for
  `koszulContractOfSequence` and the R4 corollary).
* `Algebra/Homology/HomologicalComplex.lean`: `HomologicalComplex`,
  `CochainComplex` (`ComplexShape.up`), `ChainComplex`
  (`ComplexShape.down`).
* `Algebra/Homology/ComplexShape.lean`: `ComplexShape.down` (`Rel i j` is
  definitionally `j + 1 = i`).
* `Algebra/Category/ModuleCat/Basic.lean`: `ModuleCat.of`, `ModuleCat.ofHom`.

Project (read-only): `Regularity/Koszul/AugmentedConeStep.lean` (the mapping-cone
step, extended here to all lengths from the length-1 base in §2b below).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace KoszulComplex

open CategoryTheory

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-! ## §1. Graded exterior-power modules (milestone 1) -/

/-- Graded multiplication closure for exterior powers: the product of a
degree-`i` and a degree-`j` element has degree `i + j`. Thin wrapper over the
`SetLike.GradedMonoid` instance from `ExteriorAlgebra.Grading`. -/
theorem piece_mul_mem {i j : ℕ} {a b : ExteriorAlgebra R M}
    (ha : a ∈ ⋀[R]^i M) (hb : b ∈ ⋀[R]^j M) : a * b ∈ ⋀[R]^(i + j) M :=
  SetLike.GradedMul.mul_mem ha hb

/-- The unit lives in degree zero. -/
theorem mem_piece_zero_one : (1 : ExteriorAlgebra R M) ∈ ⋀[R]^0 M :=
  SetLike.one_mem_graded _

/-- Degree-one elements are exactly the `ι`-images: `⋀¹ M = range(ι)^1`
collapses to `range(ι)` by `pow_one`. -/
theorem mem_piece_one_iff {a : ExteriorAlgebra R M} :
    a ∈ ⋀[R]^1 M ↔ ∃ m : M, ExteriorAlgebra.ι R m = a := by
  rw [show (⋀[R]^1 M : Submodule R (ExteriorAlgebra R M)) =
      LinearMap.range (ExteriorAlgebra.ι R : M →ₗ[R] ExteriorAlgebra R M) from
    pow_one _]
  exact LinearMap.mem_range

/-- Every generator `ι m` lies in the first exterior power. -/
theorem mem_ι_piece_one (m : M) : ExteriorAlgebra.ι R m ∈ ⋀[R]^1 M :=
  mem_piece_one_iff.mpr ⟨m, rfl⟩

/-- Every decomposable `ιMulti` wedge lies in the corresponding exterior power
(thin wrapper over `ExteriorAlgebra.ιMulti_range`). -/
theorem mem_ιMulti_piece (n : ℕ) (v : Fin n → M) :
    ExteriorAlgebra.ιMulti R n v ∈ ⋀[R]^n M :=
  ExteriorAlgebra.ιMulti_range R n ⟨v, rfl⟩

/-- When `M` is free, its exterior algebra is free (Mathlib basis from
`ExteriorAlgebra.Basis`). The per-degree rank formula is proved in §6
(`exteriorPower_finrank_fin_fun`). -/
noncomputable def exteriorAlgebraBasis {I : Type*} [LinearOrder I]
    (b : Module.Basis I R M) :
    Module.Basis (Finset I) R (ExteriorAlgebra R M) :=
  b.ExteriorAlgebra

/-! ## §2. The wedge differential (milestone 2) -/

/-- The Koszul differential at degree `k`: left multiplication by the charge
`ξ`, landing in degree `k + 1` by graded-multiplication closure
(`1 + k` is rewritten to `k + 1`). -/
def koszulD (ξ : ↥(⋀[R]^1 M)) (k : ℕ) :
    ↥(⋀[R]^k M) →ₗ[R] ↥(⋀[R]^(k + 1) M) where
  toFun z := ⟨(ξ : ExteriorAlgebra R M) * z, by
    have h := SetLike.GradedMul.mul_mem ξ.2 z.2
    rwa [add_comm (1 : ℕ) k] at h⟩
  map_add' x y := Subtype.ext (mul_add (ξ : ExteriorAlgebra R M) x y)
  map_smul' r x :=
    Subtype.ext (Algebra.mul_smul_comm r (ξ : ExteriorAlgebra R M) x)

/-- The differential acts by left multiplication with the charge. -/
@[simp]
theorem koszulD_apply (ξ : ↥(⋀[R]^1 M)) (k : ℕ)
    (z : ↥(⋀[R]^k M)) :
    ((koszulD ξ k z : ↥(⋀[R]^(k + 1) M)) : ExteriorAlgebra R M) =
      (ξ : ExteriorAlgebra R M) * z :=
  rfl

/-- The charge of a sequence `x : Fin n → R`: the sequence itself, viewed as an
element of `M = Fin n → R` and mapped into `⋀¹ M` by `ι`. -/
def koszulCharge {n : ℕ} (x : Fin n → R) : ↥(⋀[R]^1 (Fin n → R)) :=
  ⟨ExteriorAlgebra.ι R x, mem_piece_one_iff.mpr ⟨x, rfl⟩⟩

/-! ## §2b. Degree-one contraction (chain-form bottom map) -/

/-- Degree-one contraction along `φ : M →ₗ[R] R`: on `⋀¹ M = range(ι)` it
undoes `ι` (via `ιInv`) and applies `φ`. This is the bottom differential
`K₁ → K₀ = R` of the chain-form Koszul complex; the general-degree
contraction is proved in §5 (`koszulContract`). -/
def koszulContractOne (φ : M →ₗ[R] R) : ↥(⋀[R]^1 M) →ₗ[R] R :=
  φ.comp (ExteriorAlgebra.ιInv.comp (⋀[R]^1 M).subtype)

/-- The degree-one contraction recovers `φ` on generators. -/
theorem koszulContractOne_ι (φ : M →ₗ[R] R) (m : M)
    (h : ExteriorAlgebra.ι R m ∈ ⋀[R]^1 M) :
    koszulContractOne φ ⟨ExteriorAlgebra.ι R m, h⟩ = φ m := by
  change φ (ExteriorAlgebra.ιInv (ExteriorAlgebra.ι R m)) = φ m
  rw [ExteriorAlgebra.ι_leftInverse]

/-! ## §3. `d² = 0` (milestone 3) -/

/-- Every degree-one charge squares to zero: `ξ = ι m` for some `m`
(`mem_piece_one_iff`), and `ι m * ι m = 0` (`ι_sq_zero`). -/
theorem charge_sq_zero (ξ : ↥(⋀[R]^1 M)) :
    (ξ : ExteriorAlgebra R M) * ξ = 0 := by
  obtain ⟨m, hm⟩ := mem_piece_one_iff.mp ξ.2
  rw [← hm]
  exact ExteriorAlgebra.ι_sq_zero m

/-- The differential squares to zero: `ξ * (ξ * z) = (ξ * ξ) * z = 0`. -/
theorem koszulD_comp_koszulD (ξ : ↥(⋀[R]^1 M)) (k : ℕ) :
    (koszulD ξ (k + 1)).comp (koszulD ξ k) = 0 := by
  apply LinearMap.ext
  intro z
  refine Subtype.ext ?_
  rw [LinearMap.comp_apply, koszulD_apply, koszulD_apply,
    LinearMap.zero_apply]
  change (ξ : ExteriorAlgebra R M) *
    ((ξ : ExteriorAlgebra R M) * (z : ExteriorAlgebra R M)) = 0
  rw [← mul_assoc, charge_sq_zero ξ, zero_mul]

/-! ## §4. `HomologicalComplex` bundling (milestone 4) -/

/-- The differential transported along `i + 1 = j`, so it can serve as the
`d i j` morphism for arbitrary `j`. -/
def koszulDAt (ξ : ↥(⋀[R]^1 M)) (i j : ℕ) (h : i + 1 = j) :
    ↥(⋀[R]^i M) →ₗ[R] ↥(⋀[R]^j M) :=
  h ▸ koszulD ξ i

/-- Transport along `rfl` is the identity. -/
@[simp]
theorem koszulDAt_rfl (ξ : ↥(⋀[R]^1 M)) (i : ℕ)
    (h : i + 1 = i + 1) : koszulDAt ξ i (i + 1) h = koszulD ξ i := by
  cases h
  rfl

/-- The complex morphisms: the differential on consecutive degrees, zero
elsewhere. -/
def koszulMor (ξ : ↥(⋀[R]^1 M)) (i j : ℕ) :
    ModuleCat.of R ↥(⋀[R]^i M) ⟶ ModuleCat.of R ↥(⋀[R]^j M) :=
  dite (i + 1 = j) (fun h => ModuleCat.ofHom (koszulDAt ξ i j h))
    (fun _ => 0)

/-- On consecutive degrees the morphism is the differential. -/
theorem koszulMor_succ (ξ : ↥(⋀[R]^1 M)) (i : ℕ) :
    koszulMor ξ i (i + 1) = ModuleCat.ofHom (koszulD ξ i) := by
  have hcond : i + 1 = i + 1 := rfl
  rw [koszulMor, dite_eq_left hcond]
  exact congrArg ModuleCat.ofHom (koszulDAt_rfl ξ i hcond)

/-- Consecutive morphisms compose to zero (milestone-3 content at the
`ModuleCat` level). The `ComplexShape.up ℕ` relations are definitionally the
equations `i + 1 = j`, so `subst` applies directly. -/
theorem koszulMor_comp_zero (ξ : ↥(⋀[R]^1 M)) (i j k : ℕ)
    (hij : (ComplexShape.up ℕ).Rel i j)
    (hjk : (ComplexShape.up ℕ).Rel j k) :
    koszulMor ξ i j ≫ koszulMor ξ j k = 0 := by
  have hij' : i + 1 = j := hij
  have hjk' : j + 1 = k := hjk
  subst hij'
  subst hjk'
  rw [koszulMor_succ, koszulMor_succ, ← ModuleCat.ofHom_comp,
    koszulD_comp_koszulD, ModuleCat.ofHom_zero]

/-- The Koszul complex of the charge `ξ` as a cochain complex, hence a
`HomologicalComplex` with `ComplexShape.up ℕ`. -/
def koszulComplex (ξ : ↥(⋀[R]^1 M)) :
    CochainComplex (ModuleCat R) ℕ where
  X k := ModuleCat.of R ↥(⋀[R]^k M)
  d := koszulMor ξ
  shape := fun i j h => by
    have hne : ¬(i + 1 = j) := fun heq => h heq
    simp only [koszulMor, dite_eq_right hne]
  d_comp_d' := fun i j k hij hjk => koszulMor_comp_zero ξ i j k hij hjk

/-- The Koszul complex `K(x₁, …, xₙ)` of a sequence, as a cochain complex. -/
def koszulComplexOfSequence {n : ℕ} (x : Fin n → R) :
    CochainComplex (ModuleCat R) ℕ :=
  koszulComplex (koszulCharge x)

/-! ## §5. General contraction and the chain-form complex (R1) -/

/-- Contraction lowers degree on decomposable wedges: for `v : Fin (n+1) → M`,
contracting `ιMulti R (n+1) v` along `φ` lies in `⋀[R]^n M`. HilbertFunctionCount on
`n`, splitting off the head factor with `ιMulti_succ_apply` and using the
antiderivation law `contractLeft_ι_mul`. The exterior algebra is the Clifford
algebra at `Q = 0` (`ExteriorAlgebra` is an abbrev), so
`CliffordAlgebra.contractLeft` applies directly.
-/
theorem contractLeft_ιMulti_mem (φ : M →ₗ[R] R) (n : ℕ) :
    ∀ v : Fin (n.succ) → M,
      CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) φ
          (ExteriorAlgebra.ιMulti R (n.succ) v) ∈ ⋀[R]^n M := by
  induction n with
  | zero =>
    intro v
    have hsplit := ExteriorAlgebra.ιMulti_succ_apply (R := R) v
    rw [hsplit, CliffordAlgebra.contractLeft_ι_mul,
      ExteriorAlgebra.ιMulti_zero_apply, CliffordAlgebra.contractLeft_one,
      mul_zero, sub_zero]
    exact Submodule.smul_mem _ _ mem_piece_zero_one
  | succ n ih =>
    intro v
    have hsplit := ExteriorAlgebra.ιMulti_succ_apply (R := R) v
    rw [hsplit, CliffordAlgebra.contractLeft_ι_mul]
    refine Submodule.sub_mem (p := ⋀[R]^(n.succ) M) ?_ ?_
    · exact Submodule.smul_mem _ _ (mem_ιMulti_piece _ _)
    · rw [(by omega : n.succ = 1 + n)]
      exact piece_mul_mem (mem_ι_piece_one _) (ih _)

/-- Contraction lowers degree: `contractLeft φ` maps `⋀[R]^(k+1) M` into
`⋀[R]^k M`. The decomposable wedges span (`ιMulti_span_fixedDegree`), so the
generator case `contractLeft_ιMulti_mem` extends by `Submodule.map_span_le`.
-/
theorem koszulContract_mem (φ : M →ₗ[R] R) (k : ℕ) (z : ExteriorAlgebra R M)
    (hz : z ∈ ⋀[R]^(k + 1) M) :
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) φ z ∈ ⋀[R]^k M := by
  have hle : Submodule.map
      (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) φ)
      (⋀[R]^(k + 1) M) ≤ ⋀[R]^k M := by
    rw [← ExteriorAlgebra.ιMulti_span_fixedDegree, Submodule.map_span_le]
    intro y hy
    obtain ⟨v, rfl⟩ := hy
    exact contractLeft_ιMulti_mem φ k v
  exact hle (Submodule.mem_map_of_mem hz)

/-- The Koszul contraction at degree `k + 1`: interior product with `φ`,
landing in degree `k` by `koszulContract_mem`. This is the differential
`K_{k+1} → K_k` of the chain-form complex.
-/
def koszulContract (φ : M →ₗ[R] R) (k : ℕ) :
    ↥(⋀[R]^(k + 1) M) →ₗ[R] ↥(⋀[R]^k M) where
  toFun z := ⟨CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) φ z,
    koszulContract_mem φ k z z.2⟩
  map_add' x y := Subtype.ext
    (map_add _ (x : ExteriorAlgebra R M) (y : ExteriorAlgebra R M))
  map_smul' r x := Subtype.ext (map_smul _ r (x : ExteriorAlgebra R M))

/-- The contraction acts by `CliffordAlgebra.contractLeft`. -/
@[simp]
theorem koszulContract_apply (φ : M →ₗ[R] R) (k : ℕ)
    (z : ↥(⋀[R]^(k + 1) M)) :
    ((koszulContract φ k z : ↥(⋀[R]^k M)) : ExteriorAlgebra R M) =
      CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) φ z :=
  rfl

/-- The general contraction agrees with `koszulContractOne` on generators:
contracting `ι m` gives `φ m` (as `algebraMap _ (φ m) ∈ ⋀[R]^0 M`).
-/
theorem koszulContract_ι (φ : M →ₗ[R] R) (m : M)
    (h : ExteriorAlgebra.ι R m ∈ ⋀[R]^1 M) :
    ((koszulContract φ 0 ⟨ExteriorAlgebra.ι R m, h⟩ : ↥(⋀[R]^0 M)) :
      ExteriorAlgebra R M) = algebraMap R (ExteriorAlgebra R M) (φ m) := by
  change CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) φ
      (ExteriorAlgebra.ι R m) = algebraMap R (ExteriorAlgebra R M) (φ m)
  exact CliffordAlgebra.contractLeft_ι _ _ _

/-- The contraction squares to zero (via `contractLeft_contractLeft`).
-/
theorem koszulContract_comp (φ : M →ₗ[R] R) (k : ℕ) :
    (koszulContract φ k).comp (koszulContract φ (k + 1)) = 0 := by
  apply LinearMap.ext
  intro z
  refine Subtype.ext ?_
  rw [LinearMap.comp_apply, koszulContract_apply, koszulContract_apply,
    LinearMap.zero_apply]
  exact CliffordAlgebra.contractLeft_contractLeft (d := φ) _

/-! ## §5b. Chain-complex bundling -/

/-- The contraction transported along `j + 1 = i`, so it can serve as the
`d i j` morphism for arbitrary `j`. -/
def koszulCAt (φ : M →ₗ[R] R) (i j : ℕ) (h : j + 1 = i) :
    ↥(⋀[R]^i M) →ₗ[R] ↥(⋀[R]^j M) :=
  h ▸ koszulContract φ j

/-- Transport along `rfl` is the identity. -/
@[simp]
theorem koszulCAt_rfl (φ : M →ₗ[R] R) (j : ℕ)
    (h : j + 1 = j + 1) : koszulCAt φ (j + 1) j h = koszulContract φ j := by
  cases h
  rfl

/-- The complex morphisms: the contraction on consecutive degrees, zero
elsewhere. -/
def koszulCMor (φ : M →ₗ[R] R) (i j : ℕ) :
    ModuleCat.of R ↥(⋀[R]^i M) ⟶ ModuleCat.of R ↥(⋀[R]^j M) :=
  dite (j + 1 = i) (fun h => ModuleCat.ofHom (koszulCAt φ i j h))
    (fun _ => 0)

/-- On consecutive degrees the morphism is the contraction. -/
theorem koszulCMor_succ (φ : M →ₗ[R] R) (j : ℕ) :
    koszulCMor φ (j + 1) j = ModuleCat.ofHom (koszulContract φ j) := by
  have hcond : j + 1 = j + 1 := rfl
  rw [koszulCMor, dite_eq_left hcond]
  exact congrArg ModuleCat.ofHom (koszulCAt_rfl φ j hcond)

/-- Consecutive morphisms compose to zero. The `ComplexShape.down ℕ` relations
are definitionally the equations `j + 1 = i`, so `subst` applies directly. -/
theorem koszulCMor_comp_zero (φ : M →ₗ[R] R) (i j k : ℕ)
    (hij : (ComplexShape.down ℕ).Rel i j)
    (hjk : (ComplexShape.down ℕ).Rel j k) :
    koszulCMor φ i j ≫ koszulCMor φ j k = 0 := by
  have hij' : j + 1 = i := hij
  have hjk' : k + 1 = j := hjk
  subst hij'
  subst hjk'
  rw [koszulCMor_succ, koszulCMor_succ, ← ModuleCat.ofHom_comp,
    koszulContract_comp, ModuleCat.ofHom_zero]

/-- The Koszul chain complex of `φ` as a `ChainComplex`, hence a
`HomologicalComplex` with `ComplexShape.down ℕ`.
-/
def koszulChainComplex (φ : M →ₗ[R] R) :
    ChainComplex (ModuleCat R) ℕ where
  X k := ModuleCat.of R ↥(⋀[R]^k M)
  d := koszulCMor φ
  shape := fun i j h => by
    have hne : ¬(j + 1 = i) := fun heq => h heq
    simp only [koszulCMor, dite_eq_right hne]
  d_comp_d' := fun i j k hij hjk => koszulCMor_comp_zero φ i j k hij hjk

/-- The degree-`k` object of the Koszul chain complex. -/
theorem koszulChainComplex_X (φ : M →ₗ[R] R) (k : ℕ) :
    (koszulChainComplex φ).X k = ModuleCat.of R ↥(⋀[R]^k M) :=
  rfl

/-- The morphisms of the Koszul chain complex are `koszulCMor`. -/
theorem koszulChainComplex_d (φ : M →ₗ[R] R) :
    (koszulChainComplex φ).d = koszulCMor φ :=
  rfl

/-- The contraction functional of a sequence `x : Fin n → R`: the linear form
sending the `i`-th standard basis vector to `x i`.
-/
noncomputable def koszulContractOfSequence {n : ℕ} (x : Fin n → R) :
    (Fin n → R) →ₗ[R] R :=
  (Pi.basisFun R (Fin n)).constr R x

/-- The Koszul chain complex `K(x₁, …, xₙ)` of a sequence.
-/
noncomputable def koszulChainComplexOfSequence {n : ℕ} (x : Fin n → R) :
    ChainComplex (ModuleCat R) ℕ :=
  koszulChainComplex (koszulContractOfSequence x)

/-! ## §6. Rank formula (R4) -/

/-- Rank formula: for `M` finite free of `finrank n`, the `k`-th exterior
power has `finrank (n.choose k)`. Thin wrapper over `exteriorPower.finrank_eq`
(the per-degree basis underlying `exteriorAlgebraBasis`).
-/
theorem exteriorPower_finrank_of_finrank_eq {n k : ℕ} [Nontrivial R]
    [Module.Free R M] [Module.Finite R M] (h : Module.finrank R M = n) :
    Module.finrank R ↥(⋀[R]^k M) = n.choose k := by
  rw [exteriorPower.finrank_eq, h]

/-- Rank formula for the Koszul setting: `M = Fin m → K` over a field.
-/
theorem exteriorPower_finrank_fin_fun (K : Type*) [Field K] (m k : ℕ) :
    Module.finrank K ↥(⋀[K]^k (Fin m → K)) = m.choose k := by
  rw [exteriorPower.finrank_eq,
    Module.finrank_eq_card_basis (Pi.basisFun K (Fin m)), Fintype.card_fin]

end KoszulComplex
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
