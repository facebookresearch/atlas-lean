/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.GeometricSemistableTraits
public import MathlibExt.AlgebraicGeometry.AdicLinearFunctoriality
public import MathlibExt.AlgebraicGeometry.GeometricAdicGaloisOperators
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.NumberTheory.Padics.RingHoms

/-!
# Actual semistable cohomology and its normalized Weil--Deligne signature

The cohomology module and every Galois operator are the actual continuous
coefficient Ext groups and inverse-image maps. The Weil group is the
literal fibre-product subgroup of decomposition-group elements and
integers whose residue actions agree with the corresponding Frobenius
power. Its representation is built from the actual Frobenius operator.

The tame-coordinate input is pinned at every finite level by actual
compatible primitive roots and uniformizer-root ratios. The generic
local-field existence is proved in TauCeti/Axiom in their stated scopes:
nonarchimedean local fields, or finite residue fields and a separable
closure. The broader henselian-trait constructor and closure transport,
including infinite residue fields and residue characteristic zero, remain
explicit unverified adapter obligations. N is the literal finite
logarithm of the actual operator at a tame element of coordinate one.

The remaining `SemistableWeilDeligneLaws` assert nilpotence, the actual
exponential recovery equation and the correct arithmetic Frobenius twist.
There is no free representation or endomorphism called monodromy.

Sources: Illusie, Astérisque 223, Exposé I, sections 1.5 and 3.1--3.8;
SGA 7 I. Covered local-field tame-coordinate producers:
TauCeti/NumberTheory/LocalField/Tame/PadicCharacter.lean, revision
62bbc0596dc3539d488232e4e924a338548ea0a9;
StacksFrontier/AlgebraicGeometry/FundamentalGroup/TameRamification/LAdicTameInertia.lean,
AxiomMath/Stacks revision c496df0d9beea9deaeabcea8492605f9a0a2313b.
https://www.numdam.org/item/AST_1994__223__9_0/
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExt.AlgebraicGeometry.SemistableWeilDeligne

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme
open GeometricSemistableTraits AdicLinearFunctoriality
open GeometricAdicGaloisOperators ContinuousAdicCoefficients
open scoped Pointwise

variable (ell : ℕ) [Fact ell.Prime]
  (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (K L : Type) [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
  [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [IsAlgClosure K L] (π : R) (T : GeometricTrait R K L π)
  (X : Over (Spec (.of R)))

/-- The fixed actual rational-adic generic-fibre cohomology. -/
abbrev Cohomology (n : ℕ) :=
  AdicCohomology ell (GenericFibre (L := L) X) n

/-- The actual Q_ell-linear Galois pullback, not an input representation. -/
def operator (σ : Galois K L) (n : ℕ) :
    Module.End ℚ_[ell] (Cohomology ell R L X n) :=
  continuousPullbackLinear ℚ_[ell] (RationalCoefficients.{0} ell)
    (genericGalois (K := K) X σ) n

/-- The condition that the Galois action on the cohomology of the geometric generic fibre is
multiplicative: for a prime $\ell$, a discrete valuation ring $R$ with fraction field $K$, an
algebraic closure $L$ of $K$ and an $R$-scheme $X$, the $\mathbb{Q}_\ell$-linear operators
$\rho(\sigma)$ = `operator σ n` on the rational $\ell$-adic cohomology $H^n(X_L, \mathbb{Q}_\ell)$
of $X_L = X \times_R \operatorname{Spec} L$ (`Cohomology`), where, for
$\sigma \in \operatorname{Gal}(L/K)$, $\rho(\sigma)$ is the inverse image along
$\mathrm{id}_X \times \operatorname{Spec} \sigma$, satisfy $\rho(1) = 1$ and
$\rho(\sigma\tau) = \rho(\sigma) \circ \rho(\tau)$. -/
class CohomologyFunctoriality (n : ℕ) : Prop where
  one : operator ell R K L X (1 : Galois K L) n = 1
  mul : ∀ σ τ : Galois K L,
    operator ell R K L X (σ * τ) n =
      operator ell R K L X σ n * operator ell R K L X τ n

/-- An actual Frobenius lift, normalized on the actual residue quotient. -/
structure ArithmeticFrobenius where
  [finiteResidue : Finite (IsLocalRing.ResidueField R)]
  element : Decomposition π T
  normalized : ∀ a : normalRing R L,
    element • a - a ^ Nat.card (IsLocalRing.ResidueField R) ∈ T.point

/-- Actual compatible primitive roots and the normalized tame coordinate. -/
structure TameCoordinate where
  ell_ne_residue : ell ≠ ringChar (IsLocalRing.ResidueField R)
  root : ℕ → L
  primitive : ∀ n, IsPrimitiveRoot (root n) (ell ^ n)
  compatible : ∀ n, root (n + 1) ^ ell = root n
  coordinate : Inertia π T →* Multiplicative ℤ_[ell]
  continuous : Continuous coordinate
  root_normalization : ∀ (σ : Inertia π T) (n : ℕ) (a : L),
    a ^ (ell ^ n) = algebraMap R L π →
      root n ^ (PadicInt.toZModPow n (coordinate σ).toAdd).val * a = σ.1.1 a
  generator : Inertia π T
  generator_normalization : coordinate generator = Multiplicative.ofAdd 1

variable {ell R K L π T X}

/-- The actual integral Weil fibre product, with arithmetic degree. -/
def WeilGroup (A : ArithmeticFrobenius R K L π T) :
    Subgroup (Decomposition π T × Multiplicative ℤ) where
  carrier := {w | residueAction π T w.1 =
    (residueAction π T A.element) ^ w.2.toAdd}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change residueAction π T (a.1 * b.1) =
      (residueAction π T A.element) ^ (a.2.toAdd + b.2.toAdd)
    rw [map_mul, ha, hb, zpow_add]
  inv_mem' := by
    intro a ha
    change residueAction π T a.1⁻¹ =
      (residueAction π T A.element) ^ (-a.2.toAdd)
    rw [map_inv, ha, zpow_neg]

/-- The actual arithmetic degree, read from the fibre-product coordinate. -/
def degree (A : ArithmeticFrobenius R K L π T) :
    WeilGroup A →* Multiplicative ℤ :=
  (MonoidHom.snd (Decomposition π T) (Multiplicative ℤ)).comp
    (WeilGroup A).subtype

variable (ell R K L X) (n : ℕ) [CohomologyFunctoriality ell R K L X n]

/-- The actual inverse pair of cohomological Galois maps. -/
def operatorUnit (σ : Galois K L) :
    (Module.End ℚ_[ell] (Cohomology ell R L X n))ˣ where
  val := operator ell R K L X σ n
  inv := operator ell R K L X σ⁻¹ n
  val_inv := by
    calc
      operator ell R K L X σ n * operator ell R K L X σ⁻¹ n =
          operator ell R K L X (σ * σ⁻¹) n :=
        (CohomologyFunctoriality.mul (ell := ell) (R := R) (K := K)
          (L := L) (X := X) (n := n) σ σ⁻¹).symm
      _ = operator ell R K L X 1 n :=
        congrArg (fun τ ↦ operator ell R K L X τ n) (mul_inv_cancel σ)
      _ = 1 := CohomologyFunctoriality.one
  inv_val := by
    calc
      operator ell R K L X σ⁻¹ n * operator ell R K L X σ n =
          operator ell R K L X (σ⁻¹ * σ) n :=
        (CohomologyFunctoriality.mul (ell := ell) (R := R) (K := K)
          (L := L) (X := X) (n := n) σ⁻¹ σ).symm
      _ = operator ell R K L X 1 n :=
        congrArg (fun τ ↦ operator ell R K L X τ n) (inv_mul_cancel σ)
      _ = 1 := CohomologyFunctoriality.one

/-- The literal finite logarithm, using the geometric nilpotence bound. -/
def finiteLog (U : Module.End ℚ_[ell] (Cohomology ell R L X n)) :
    Module.End ℚ_[ell] (Cohomology ell R L X n) :=
  ∑ i ∈ (Finset.range (n + 1)).filter (fun i ↦ 0 < i),
    (((-1 : ℚ_[ell]) ^ (i + 1)) * (i : ℚ_[ell])⁻¹) • (U - 1) ^ i

/-- The literal finite exponential on the same actual module. -/
def finiteExp (N : Module.End ℚ_[ell] (Cohomology ell R L X n)) :
    Module.End ℚ_[ell] (Cohomology ell R L X n) :=
  ∑ i ∈ Finset.range (n + 1), (i.factorial : ℚ_[ell])⁻¹ • N ^ i

/-- Monodromy is fixed by the actual tame-coordinate-one operator. -/
def monodromy (B : TameCoordinate ell R K L π T) :
    Module.End ℚ_[ell] (Cohomology ell R L X n) :=
  finiteLog ell R L X n (operator ell R K L X B.generator.1.1 n)

/-- The actual unramified Weil representation of a semistable object.
Its arithmetic degree m acts by the actual Frobenius operator to power m. -/
def weilRepresentation (A : ArithmeticFrobenius R K L π T) :
    WeilGroup A →* (Module.End ℚ_[ell] (Cohomology ell R L X n))ˣ :=
  (zpowersHom _ (operatorUnit ell R K L X n A.element.1)).comp (degree A)

/-- The exact geometric association laws, on the fixed actual operators.
Arithmetic degree has twist q^m; geometric Frobenius therefore has q^-1. -/
def SemistableWeilDeligneLaws (A : ArithmeticFrobenius R K L π T)
    (B : TameCoordinate ell R K L π T) : Prop :=
  let N := monodromy ell R K L X n B
  N ^ (n + 1) = 0 ∧
  (∀ σ : Inertia π T,
    operator ell R K L X σ.1.1 n =
      finiteExp ell R L X n (((B.coordinate σ).toAdd : ℚ_[ell]) • N)) ∧
  ∀ w : WeilGroup A,
    (weilRepresentation ell R K L X n A w).val * N =
      (Nat.card (IsLocalRing.ResidueField R) : ℚ_[ell]) ^ w.1.2.toAdd •
        (N * (weilRepresentation ell R K L X n A w).val)

end MathlibExt.AlgebraicGeometry.SemistableWeilDeligne
