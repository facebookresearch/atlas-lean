/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.Additive.CovBySMul

import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Basis-vector lower bound for binary coset covers

Every admissible asymptotic coset-cover exponent over the two-element field is at least one.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.PolynomialFreimanRuzsaBinaryWanted

open scoped Pointwise

/-- **The binary vector space $\mathbb{F}_2^n$.** For a natural number $n$, the ambient space
$\mathbb{F}_2^n$ of all functions from $\{0, 1, \dots, n - 1\}$ to the two-element field
$\mathbb{F}_2 = \mathbb{Z}/2\mathbb{Z}$.

Source: Optimization Problems constant 18a. -/
abbrev BinaryAmbientSpace (n : ℕ) := Fin n → ZMod 2

/--
**Admissible asymptotic coset-cover exponents.** A real number $C$ is an admissible asymptotic
coset-cover exponent if for every real $\varepsilon > 0$ there is a real $K_0 \ge 1$ such that
for every real $K \ge K_0$, every $n \in \mathbb{N}$ and every nonempty finite set
$A \subseteq \mathbb{F}_2^n$ with $|A + A| \le K|A|$, there is an $\mathbb{F}_2$-linear subspace
$H$ of $\mathbb{F}_2^n$ with $|H| \le |A|$ such that $A$ is covered by at most $K^{C + \varepsilon}$
translates of $H$: there is a finite set $F \subseteq \mathbb{F}_2^n$ with
$|F| \le K^{C + \varepsilon}$ and $A \subseteq F + H$.

This makes the source's bound of $K^{C + o(1)}$ translates uniform: once $K$ is large enough,
the same bound works in every dimension and for every nonempty set of doubling at most $K$.

Source: Optimization Problems constant 18a, with the uniform asymptotic
quantifiers made explicit. -/
def IsAsymptoticCosetCoverExponent (C : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ K₀ : ℝ, 1 ≤ K₀ ∧
      ∀ K : ℝ, K₀ ≤ K →
        ∀ (n : ℕ) (A : Finset (BinaryAmbientSpace n)), A.Nonempty →
          ((A + A).card : ℝ) ≤ K * (A.card : ℝ) →
            ∃ H : Submodule (ZMod 2) (BinaryAmbientSpace n),
              Nat.card H ≤ A.card ∧
                CovByVAdd (BinaryAmbientSpace n) (Real.rpow K (C + ε))
                  (A : Set (BinaryAmbientSpace n)) (H : Set (BinaryAmbientSpace n))

/-- **Statement of the basis-vector lower bound.** The proposition that every admissible
asymptotic coset-cover exponent $C$ satisfies $C \ge 1$.

The obstruction comes from sets of basis vectors.

Source: Optimization Problems constant 18a. -/
def basisVectorsLowerBound1 : Prop :=
  ∀ C : ℝ, IsAsymptoticCosetCoverExponent C → 1 ≤ C

private theorem two_mul_le_two_pow (d : ℕ) : 2 * d ≤ 2 ^ d := by
  cases d with
  | zero => simp
  | succ d =>
    rw [pow_succ]
    have := d.lt_two_pow_self
    omega

private theorem finrank_le_add_card_of_basis_cover {n : ℕ}
    (b : Module.Basis (Fin n) (ZMod 2) (BinaryAmbientSpace n))
    (H : Submodule (ZMod 2) (BinaryAmbientSpace n)) (F : Finset (BinaryAmbientSpace n))
    (hcover : Set.range b ⊆ (F : Set (BinaryAmbientSpace n)) + (H : Set (BinaryAmbientSpace n))) :
    n ≤ Module.finrank (ZMod 2) H + F.card := by
  let S := Submodule.span (ZMod 2) (F : Set (BinaryAmbientSpace n))
  -- Every basis vector lies in the sum of the covering subspace and the span of the translates.
  have htop : H ⊔ S = ⊤ := by
    apply top_unique
    rw [← b.span_eq, Submodule.span_le]
    intro v hv
    obtain ⟨f, hf, x, hx, rfl⟩ := Set.mem_add.mp (hcover hv)
    rw [add_comm]
    exact Submodule.add_mem_sup hx (Submodule.subset_span hf)
  calc
    n = Module.finrank (ZMod 2) (H ⊔ S : Submodule (ZMod 2) (BinaryAmbientSpace n)) := by
      rw [htop, finrank_top, Module.finrank_fin_fun]
    _ ≤ Module.finrank (ZMod 2) H + Module.finrank (ZMod 2) S :=
      Submodule.finrank_add_le_finrank_add_finrank H S
    _ ≤ Module.finrank (ZMod 2) H + F.card :=
      Nat.add_le_add_left (finrank_span_finset_le_card F) _

/-- **Basis-vector lower bound for coset-cover exponents.** Every admissible asymptotic
coset-cover exponent $C$ satisfies $C \ge 1$.

The obstruction comes from sets of basis vectors.

Source: Optimization Problems constant 18a. -/
public theorem basisVectorsLowerBound1_holds : basisVectorsLowerBound1 := by
  intro C hC
  by_contra! hC_lt
  classical
  let ε : ℝ := (1 - C) / 2
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  have hgap : 0 < 1 - (C + ε) := by
    dsimp [ε]
    linarith
  obtain ⟨K₀, hK₀, hK⟩ := hC ε hε
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp ((tendsto_rpow_atTop hgap).eventually_gt_atTop 2)
  obtain ⟨n, hn⟩ := exists_nat_ge (max K₀ T)
  have hnK : K₀ ≤ (n : ℝ) := (le_max_left _ _).trans hn
  have hn_pos : 0 < (n : ℝ) := zero_lt_one.trans_le (hK₀.trans hnK)
  have hn_pow : (n : ℝ) ^ (C + ε) < n / 2 := by
    have h := hT (n : ℝ) ((le_max_right _ _).trans hn)
    rw [Real.rpow_sub hn_pos, Real.rpow_one] at h
    have h' := (lt_div_iff₀ (Real.rpow_pos_of_pos hn_pos (C + ε))).mp h
    linarith
  let b := Pi.basisFun (ZMod 2) (Fin n)
  let A : Finset (BinaryAmbientSpace n) := Finset.univ.image b
  have hA : A.card = n := by
    simp [A, Finset.card_image_of_injective _ b.injective]
  have hA_nonempty : A.Nonempty := Finset.card_pos.mp (hA.symm ▸ Nat.cast_pos.mp hn_pos)
  have hdoubling : ((A + A).card : ℝ) ≤ (n : ℝ) * A.card := by
    have h : ((A + A).card : ℝ) ≤ (A.card : ℝ) * A.card := by
      exact_mod_cast Finset.card_add_le (s := A) (t := A)
    simpa only [hA] using h
  obtain ⟨H, hH, F, hF, hcover⟩ := hK n hnK n A hA_nonempty hdoubling
  have hcover' :
      Set.range b ⊆ (F : Set (BinaryAmbientSpace n)) + (H : Set (BinaryAmbientSpace n)) := by
    rintro _ ⟨i, rfl⟩
    exact hcover (Finset.mem_image_of_mem b (Finset.mem_univ i))
  have hrank := finrank_le_add_card_of_basis_cover b H F hcover'
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hA] at hH
  have hdim : 2 * Module.finrank (ZMod 2) H ≤ n := (two_mul_le_two_pow _).trans hH
  have hrank_real : (n : ℝ) ≤ (Module.finrank (ZMod 2) H : ℝ) + F.card := by exact_mod_cast hrank
  have hdim_real : 2 * (Module.finrank (ZMod 2) H : ℝ) ≤ n := by exact_mod_cast hdim
  linarith [hF.trans_lt hn_pow]

end MathlibExt.Combinatorics.PolynomialFreimanRuzsaBinaryWanted
