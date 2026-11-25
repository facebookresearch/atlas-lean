/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import MathlibExt.Analysis.Fourier.FiniteAbelianDFT

/-!
# Units in the integral group ring of C₂ × C₂ × C₂ × C₆

Every unit is a signed group element (`conjecture_refuted`). Character evaluations lie in
the Eisenstein integers, so a unit has squared norm one at every character. Plancherel then
shows that the integer coefficients of the unit have sum of squares one.
-/

@[expose] public section

namespace MathlibExt.Algebra.ExoticUnitsC2C2C2C6Wanted

/-- **The group $C_2 \times C_2 \times C_2 \times C_6$.** The abelian group
$G = C_2 \times C_2 \times C_2 \times C_6$, the product of cyclic groups of orders $2$, $2$, $2$
and $6$, written additively as
$\mathbb{Z}/2 \times \mathbb{Z}/2 \times \mathbb{Z}/2 \times \mathbb{Z}/6$.

Source: `OWR-11129-005` (Computational Group Theory (2012), Oberwolfach Reports,
DOI 10.4171/owr/2011/37). -/
abbrev OWRGroup : Type := ZMod 2 × ZMod 2 × ZMod 2 × ZMod 6

/-- **The integral group ring of $C_2 \times C_2 \times C_2 \times C_6$.** The integral group
ring $\mathbb{Z}G$ of $G = C_2 \times C_2 \times C_2 \times C_6$: finitely supported formal
$\mathbb{Z}$-linear combinations of elements of $G$, with the product extending the group
operation of $G$ bilinearly.

Source: `OWR-11129-005` (Computational Group Theory (2012), Oberwolfach Reports,
DOI 10.4171/owr/2011/37). -/
abbrev OWRGroupRing : Type := AddMonoidAlgebra ℤ OWRGroup

/-- **Exotic unit conjecture for $C_2 \times C_2 \times C_2 \times C_6$.** Let
$G = C_2 \times C_2 \times C_2 \times C_6$. The statement that the integral group ring
$\mathbb{Z}G$ contains an exotic unit: a unit $u$ with $u \ne g$ and $u \ne -g$ for every
$g \in G$.

Source: the open question of `OWR-11129-005` (Computational Group Theory (2012),
Oberwolfach Reports, DOI 10.4171/owr/2011/37). -/
def conjecture : Prop :=
  ∃ u : OWRGroupRingˣ, ∀ g : OWRGroup, ∀ s : ℤˣ,
    (↑u : OWRGroupRing) ≠ AddMonoidAlgebra.single g (↑s : ℤ)

open MathlibExt.Analysis.Fourier.FiniteAbelianDFTWanted

private noncomputable abbrev evalChar (χ : AddChar OWRGroup ℂ) : OWRGroupRing →ₐ[ℤ] ℂ :=
  AddMonoidAlgebra.lift ℤ ℂ OWRGroup χ.toMonoidHom

private lemma evalChar_eq_dft (χ : AddChar OWRGroup ℂ) (x : OWRGroupRing) :
    evalChar χ x = dftFun (fun g => (x.coeff g : ℂ)) χ := by
  rw [AddMonoidAlgebra.lift_apply', Finsupp.sum_fintype _ _ (by simp)]
  simp [dftFun, mul_comm]

/-- Multiplication by a primitive sixth root preserves its integer span with 1. -/
private lemma pow_coordinates {ζ : ℂ} (hζ : ζ ^ 2 - ζ + 1 = 0) (n : ℕ) :
    ∃ a b : ℤ, ζ ^ n = a + b * ζ := by
  induction n with
  | zero => exact ⟨1, 0, by simp⟩
  | succ n ih =>
    obtain ⟨a, b, hab⟩ := ih
    refine ⟨-b, a + b, ?_⟩
    rw [pow_succ, hab]
    push_cast
    linear_combination (b : ℂ) * hζ

private lemma evalChar_coordinates (χ : AddChar OWRGroup ℂ) (x : OWRGroupRing)
    {ζ : ℂ} (hprim : IsPrimitiveRoot ζ 6) (hζ : ζ ^ 2 - ζ + 1 = 0) :
    ∃ a b : ℤ, evalChar χ x = a + b * ζ := by
  have coords (g : OWRGroup) : ∃ a b : ℤ, χ g = a + b * ζ := by
    have hexp : ∀ g : OWRGroup, 6 • g = 0 := by decide
    have hχ : χ g ^ 6 = 1 := by rw [← χ.map_nsmul_eq_pow, hexp, χ.map_zero_eq_one]
    obtain ⟨n, -, hn⟩ := hprim.eq_pow_of_pow_eq_one hχ
    rw [← hn]
    exact pow_coordinates hζ n
  choose a b hab using coords
  refine ⟨∑ g, a g * x.coeff g, ∑ g, b g * x.coeff g, ?_⟩
  rw [evalChar_eq_dft, dftFun]
  push_cast
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro g _
  rw [hab]
  ring

/-- The squared norm on the Eisenstein integers is integer valued. -/
private lemma evalChar_normSq_int (χ : AddChar OWRGroup ℂ) (x : OWRGroupRing) :
    ∃ m : ℤ, Complex.normSq (evalChar χ x) = m := by
  let ζ := Complex.exp (2 * Real.pi * Complex.I / (6 : ℕ))
  have hprim : IsPrimitiveRoot ζ 6 := Complex.isPrimitiveRoot_exp 6 (by decide)
  have hζ : ζ ^ 2 - ζ + 1 = 0 := by
    simpa [Polynomial.IsRoot, Polynomial.cyclotomic_six] using
      hprim.isRoot_cyclotomic (by decide)
  have hnorm : Complex.normSq ζ = 1 := by
    rw [Complex.normSq_eq_norm_sq, hprim.norm'_eq_one (by decide), one_pow]
  have hmul : star ζ * ζ = 1 := by
    simpa [← Complex.normSq_eq_conj_mul_self] using
      (congrArg ((↑) : ℝ → ℂ) hnorm)
  have hconj : star ζ = 1 - ζ := by
    apply mul_right_cancel₀ (hprim.ne_zero (by decide) : ζ ≠ 0)
    rw [hmul]
    linear_combination hζ
  obtain ⟨a, b, hab⟩ := evalChar_coordinates χ x hprim hζ
  refine ⟨a ^ 2 + a * b + b ^ 2, ?_⟩
  apply Complex.ofReal_injective
  rw [Complex.normSq_eq_conj_mul_self, hab]
  change star ((a : ℂ) + b * ζ) * _ = _
  simp only [star_add, star_mul', star_intCast, hconj]
  push_cast
  linear_combination -(b : ℂ) ^ 2 * hζ

private lemma evalChar_unit_normSq (χ : AddChar OWRGroup ℂ) (u : OWRGroupRingˣ) :
    Complex.normSq (evalChar χ u) = 1 := by
  obtain ⟨m, hm⟩ := evalChar_normSq_int χ u
  obtain ⟨n, hn⟩ := evalChar_normSq_int χ (↑u⁻¹)
  have hmn : (m : ℝ) * n = 1 := by
    rw [← hm, ← hn, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  have hu := Int.eq_one_or_neg_one_of_mul_eq_one (show m * n = 1 by exact_mod_cast hmn)
  have hnonneg := Complex.normSq_nonneg (evalChar χ u)
  rcases hu with rfl | rfl <;> norm_num at hm <;> linarith

private lemma unit_sum_sq (u : OWRGroupRingˣ) :
    ∑ g, ((u : OWRGroupRing).coeff g) ^ 2 = 1 := by
  classical
  let f (g : OWRGroup) : ℂ := (u : OWRGroupRing).coeff g
  have hχ (χ : AddChar OWRGroup ℂ) : star (dftFun f χ) * dftFun f χ = 1 := by
    rw [← evalChar_eq_dft]
    simpa [← Complex.normSq_eq_conj_mul_self] using
      congrArg ((↑) : ℝ → ℂ) (evalChar_unit_normSq χ u)
  have hcard : (Fintype.card OWRGroup : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have h := dft_plancherel f f
  simp only [hχ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, AddChar.card_eq,
    inv_mul_cancel₀ hcard, f, star_intCast, ← sq] at h
  exact_mod_cast h

/--
**No exotic units in the integral group ring of $C_2 \times C_2 \times C_2 \times C_6$.** Let
$G = C_2 \times C_2 \times C_2 \times C_6$. Every unit $u$ of the integral group ring
$\mathbb{Z}G$ is trivial: $u = g$ or $u = -g$ for some $g \in G$.

Classical: G. Higman (1940) showed the integral group ring of an abelian group
of exponent dividing 4 or 6 has only the units $\pm g$. Via the cut-group criterion in Bächle
(arXiv:1701.04347, Prop. 2.2), $C_2^3 \times C_6$ (exponent 6) is an abelian cut group, so every
unit of $\mathbb{Z}G$ is trivial and no exotic unit exists.

Source: Andreas Bächle, Integral group rings of solvable groups with trivial central units,
Forum Math. 30 (2018), arXiv:1701.04347, https://arxiv.org/abs/1701.04347. Moved from
`OpenConjectures/Algebra/ExoticUnitsC2C2C2C6`.
-/
public theorem conjecture_refuted : ¬ conjecture := by
  classical
  rintro ⟨u, hu⟩
  let c := (u : OWRGroupRing).coeff
  have hsum : ∑ g, c g ^ 2 = 1 := unit_sum_sq u
  obtain ⟨g, -, hg⟩ := (Finset.sum_pos_iff_of_nonneg
    (fun i (_ : i ∈ Finset.univ) => sq_nonneg (c i))).1 (show 0 < ∑ i, c i ^ 2 by omega)
  have hrest := Finset.sum_erase_add (s := Finset.univ) (fun i => c i ^ 2) (Finset.mem_univ g)
  have hnonneg := Finset.sum_nonneg (s := Finset.univ.erase g) (fun i _ => sq_nonneg (c i))
  have hsq : c g ^ 2 = 1 := by omega
  have hzero : ∀ i ∈ Finset.univ.erase g, c i ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (c i))).1 (by omega)
  obtain ⟨s, hs⟩ : IsUnit (c g) := Int.isUnit_iff.2 (sq_eq_one_iff.1 hsq)
  apply hu g s
  ext i
  by_cases hi : i = g
  · subst i
    simpa [c] using hs.symm
  · have hi0 := hzero i (Finset.mem_erase.2 ⟨hi, Finset.mem_univ _⟩)
    simpa [c, AddMonoidAlgebra.coeff_single, Finsupp.single_apply, Ne.symm hi] using
      (pow_eq_zero_iff (by decide : 2 ≠ 0)).1 hi0

end MathlibExt.Algebra.ExoticUnitsC2C2C2C6Wanted
