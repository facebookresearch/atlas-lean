/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.UnitaryGroup
import MathlibExt.GroupTheory.SU2Basic
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.NumberTheory.Zsqrtd.ToReal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# Groups with one irreducible representation of each dimension (Kourovka Notebook Problem 16.58)

Kourovka Notebook, Archive of Solved Problems, Problem 16.58 (J. McKay): is `SU₂(ℂ)` the only group
that has just one irreducible complex representation of dimension `n` for each `n = 1, 2, …`?

The entrywise twist of the natural representation by a field automorphism moving `√2`
refutes this characterization.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.58 (J.
McKay). UnsolvedMath record UM-00701250 (`KOU-16.58`), dataset ulamai/UnsolvedMath v1.8.0.

Representations are all homomorphisms `G →* GLₙ(ℂ)` of the abstract group, without continuity, as in
the Archive's answer; irreducible means no invariant subspace other than `0` and `ℂⁿ`, and "just
one" means one up to conjugation by `GLₙ(ℂ)`. "`SU₂(ℂ)` is the only such group" is stated as: a
group in `Type` has the property if and only if it is isomorphic to `SU₂(ℂ)`
(`Matrix.specialUnitaryGroup (Fin 2) ℂ`).
-/

@[expose] public section

namespace MathlibExt.GroupTheory.UniqueIrreducibleRepresentationsSU2Kourovka16Problem58Wanted

/-- **Irreducible representations into $\mathrm{GL}_n(\mathbb{C})$.** Let $G$ be a group and
$\rho \colon G \to \mathrm{GL}_n(\mathbb{C})$ a homomorphism. Then $\rho$ is irreducible when
$n \ge 1$ and the only subspaces $W$ of $\mathbb{C}^n$ with $\rho(g)v \in W$ for all $g \in G$ and
$v \in W$ are $0$ and $\mathbb{C}^n$. -/
def IsIrreducibleRep {G : Type*} [Group G] {n : ℕ}
    (ρ : G →* Matrix.GeneralLinearGroup (Fin n) ℂ) : Prop :=
  0 < n ∧ ∀ W : Submodule ℂ (Fin n → ℂ),
    (∀ g : G, ∀ v ∈ W, (ρ g : Matrix (Fin n) (Fin n) ℂ).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤

/-- **Equivalent representations into $\mathrm{GL}_n(\mathbb{C})$.** Let $G$ be a group. Two
homomorphisms $\rho, \sigma \colon G \to \mathrm{GL}_n(\mathbb{C})$ are equivalent when there is a
matrix $P \in \mathrm{GL}_n(\mathbb{C})$ with $\sigma(g) = P \rho(g) P^{-1}$ for all $g \in G$. -/
def IsEquivalentRep {G : Type*} [Group G] {n : ℕ}
    (ρ σ : G →* Matrix.GeneralLinearGroup (Fin n) ℂ) : Prop :=
  ∃ P : Matrix.GeneralLinearGroup (Fin n) ℂ, ∀ g : G, σ g = P * ρ g * P⁻¹

/-- **Groups with exactly one irreducible representation of each dimension.** A group $G$ has
exactly one irreducible complex representation of each dimension when for every $n \ge 1$ there
is an irreducible homomorphism $G \to \mathrm{GL}_n(\mathbb{C})$ and any two irreducible
homomorphisms $G \to \mathrm{GL}_n(\mathbb{C})$ are equivalent. Representations are arbitrary
homomorphisms of the abstract group $G$; no continuity is required. -/
def HasUniqueIrreducibleRepOfEachDim (G : Type*) [Group G] : Prop :=
  ∀ n : ℕ, 0 < n →
    (∃ ρ : G →* Matrix.GeneralLinearGroup (Fin n) ℂ, IsIrreducibleRep ρ) ∧
    ∀ ρ σ : G →* Matrix.GeneralLinearGroup (Fin n) ℂ,
      IsIrreducibleRep ρ → IsIrreducibleRep σ → IsEquivalentRep ρ σ

/-- **McKay's question on $\mathrm{SU}_2(\mathbb{C})$ (Kourovka 16.58).** A group $G$ has exactly
one irreducible complex representation of each dimension $n = 1, 2, \dots$, up to equivalence, if
and only if $G$ is isomorphic to $\mathrm{SU}_2(\mathbb{C})$. Here a representation of dimension
$n$ is any homomorphism $G \to \mathrm{GL}_n(\mathbb{C})$ of abstract groups, with no continuity
required. -/
def su2OnlyGroupWithUniqueIrreducibleReps : Prop :=
  ∀ (G : Type) [Group G],
    HasUniqueIrreducibleRepOfEachDim G ↔ Nonempty (G ≃* Matrix.specialUnitaryGroup (Fin 2) ℂ)

open Matrix

private abbrev SU := specialUnitaryGroup (Fin 2) ℂ

/-- Extend an automorphism of the coefficient ring by fixing a transcendence basis
and then extending to the algebraic closure. -/
private theorem exists_ringEquiv_extending (R : Type) [CommRing R] [Nontrivial R]
    [Algebra R ℂ] [FaithfulSMul R ℂ] (τ : R ≃+* R) :
    ∃ σ : ℂ ≃+* ℂ, ∀ r : R, σ (algebraMap R ℂ r) = algebraMap R ℂ (τ r) := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis R ℂ
  let A := Algebra.adjoin R (Set.range ((↑) : s → ℂ))
  let : IsAlgClosure A ℂ := IsAlgClosed.isAlgClosure_of_transcendence_basis _ hs
  let e := hs.1.aevalEquiv
  let f : A ≃+* A := e.symm.toRingEquiv.trans
    ((MvPolynomial.mapEquiv s τ).trans e.toRingEquiv)
  refine ⟨IsAlgClosure.equivOfEquiv ℂ ℂ f, fun r => ?_⟩
  rw [IsScalarTower.algebraMap_apply R A ℂ, IsAlgClosure.equivOfEquiv_algebraMap]
  change algebraMap A ℂ (e (MvPolynomial.map τ (e.symm (algebraMap R A r)))) = _
  rw [e.symm.commutes, MvPolynomial.algebraMap_eq, MvPolynomial.map_C]
  exact congrArg (algebraMap A ℂ) (e.commutes (τ r))

private theorem exists_negate_sqrt_two :
    ∃ σ : ℂ ≃+* ℂ, σ (Real.sqrt 2 : ℂ) = -(Real.sqrt 2 : ℂ) := by
  let f := Complex.ofRealHom.comp (Zsqrtd.toReal (d := 2) (by decide))
  let := f.toAlgebra
  let : FaithfulSMul (ℤ√2) ℂ := (faithfulSMul_iff_algebraMap_injective _ _).2
    (Complex.ofReal_injective.comp (Zsqrtd.toReal_injective (by decide)
      (fun n hn => Int.prime_two.not_isSquare ⟨n, hn⟩)))
  obtain ⟨σ, hσ⟩ := exists_ringEquiv_extending (ℤ√2) starRingAut
  refine ⟨σ, ?_⟩
  have h := hσ Zsqrtd.sqrtd
  change σ (f Zsqrtd.sqrtd) = f (star Zsqrtd.sqrtd) at h
  simpa [f, Zsqrtd.toReal_apply] using h

/-- Apply a field automorphism to the entries of the defining representation. -/
private def twist (σ : ℂ →+* ℂ) : SU →* GL (Fin 2) ℂ :=
  (GeneralLinearGroup.map σ).comp (specialUnitaryGroup (Fin 2) ℂ).subtype.toHomUnits

private theorem twist_irreducible (σ : ℂ →+* ℂ) : IsIrreducibleRep (twist σ) := by
  refine ⟨by decide, fun W hW => ?_⟩
  let k := σ Complex.I
  have hk : k ≠ 0 := (map_ne_zero σ).2 Complex.I_ne_zero
  -- The diagonal element separates the coordinates, and the antidiagonal interchanges them.
  have diag (v : Fin 2 → ℂ) (hv : v ∈ W) : ![k * v 0, -k * v 1] ∈ W := by
    convert hW ⟨_, SU2.diag_I_mem⟩ v hv using 1
    ext i
    fin_cases i <;> simp [twist, mulVec, dotProduct, Fin.sum_univ_two, k]
  have skew (v : Fin 2 → ℂ) (hv : v ∈ W) : ![v 1, -v 0] ∈ W := by
    convert hW ⟨_, SU2.antidiag_mem⟩ v hv using 1
    ext i
    fin_cases i <;> simp [twist, mulVec, dotProduct, Fin.sum_univ_two]
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  obtain ⟨w, hw, hw0⟩ : ∃ w ∈ W, w 0 ≠ 0 := by
    by_cases h : v 0 = 0
    · refine ⟨_, skew v hv, ?_⟩
      change v 1 ≠ 0
      intro h1
      exact hv0 (by ext i; fin_cases i <;> assumption)
    · exact ⟨v, hv, h⟩
  have he : ![(1 : ℂ), 0] ∈ W := by
    convert W.smul_mem (2 * k * w 0)⁻¹ (W.add_mem (W.smul_mem k hw) (diag w hw)) using 1
    ext i
    fin_cases i <;> simp [Matrix.vecHead, Matrix.vecTail, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  apply eq_top_iff.2
  intro u _
  convert W.sub_mem (W.smul_mem (u 0) he) (W.smul_mem (u 1) (skew _ he)) using 1
  ext i
  fin_cases i <;> simp

/-- Rotation through an eighth of a turn has trace √2. -/
private theorem exists_trace_sqrt_two : ∃ g : SU, g.val.trace = (Real.sqrt 2 : ℂ) := by
  let r := Real.sqrt 2 / 2
  refine ⟨⟨!![(r : ℂ), (r : ℂ); -(r : ℂ), (r : ℂ)], ?_⟩, ?_⟩
  · apply mem_specialUnitaryGroup_fin_two_iff.2
    refine ⟨r, r, by simp, ?_⟩
    simp only [Complex.normSq_ofReal, r]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  · simp [Matrix.trace, Fin.sum_univ_two, r]

/-- **McKay's question 16.58 has a negative answer.** It is not the case that a group has exactly
one irreducible complex representation of each dimension $n \ge 1$, up to equivalence, if and only
if it is isomorphic to $\mathrm{SU}_2(\mathbb{C})$. Here a representation of dimension $n$ is any
homomorphism to $\mathrm{GL}_n(\mathbb{C})$ of abstract groups, with no continuity required.

Applying a field automorphism $\varphi$ of $\mathbb{C}$ to matrix entries gives irreducible
$2$-dimensional representations $x \mapsto x^\varphi$ of the abstract group
$\mathrm{SU}_2(\mathbb{C})$, infinitely many of them pairwise non-equivalent (von Neumann), so
$\mathrm{SU}_2(\mathbb{C})$ itself lacks the property. It does have it if only unitary
representations are counted, as these are continuous (Cartan).

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group
Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems,
Problem 16.58 (J. McKay); resolution: V. P. Burichenko, letter of 16 July 2013, as recorded in the
Kourovka Archive (observation of J. von Neumann), Kourovka Archive, Problem 16.58 (No: for field
automorphisms φ of ℂ the representations x ↦ x^φ of SU₂(ℂ) are irreducible and infinitely many are
pairwise non-equivalent, so SU₂(ℂ) itself lacks the property; it has it for unitary representations,
which are continuous by É. Cartan).
-/
theorem su2OnlyGroupWithUniqueIrreducibleReps_refuted :
    ¬ su2OnlyGroupWithUniqueIrreducibleReps := by
  intro h
  obtain ⟨σ, hσ⟩ := exists_negate_sqrt_two
  obtain ⟨g, hg⟩ := exists_trace_sqrt_two
  have unique := (h SU).2 ⟨MulEquiv.refl _⟩ 2 (by decide)
  obtain ⟨P, hP⟩ := unique.2 _ _ (twist_irreducible (RingHom.id ℂ))
    (twist_irreducible σ.toRingHom)
  have ht := congrArg (fun A : GL (Fin 2) ℂ => A.val.trace) (hP g)
  change (g.val.map σ).trace = (P.val * g.val * (P⁻¹).val).trace at ht
  rw [Matrix.trace_units_conj, ← AddMonoidHom.map_trace σ, hg, hσ] at ht
  have hpos := Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)
  have heq := congrArg Complex.re ht
  simp at heq
  linarith

end MathlibExt.GroupTheory.UniqueIrreducibleRepresentationsSU2Kourovka16Problem58Wanted
