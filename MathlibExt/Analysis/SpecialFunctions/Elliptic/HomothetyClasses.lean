/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.QuadraticForms.RootLattice
public import MathlibExt.NumberTheory.QuadraticForms.ProperIdealRootLattice

/-!
# Homothety classes of period pairs

For period pairs `L`, `L'` whose lattices satisfy `Λ' = cΛ` with `c ≠ 0`, the lattice invariants
scale as `G_n(L') = c⁻ⁿ G_n(L)` for `n ≥ 3` (for `n ≤ 2` the series diverges and both sides are
`0` by the `tsum` convention), so `g₂(L') = c⁻⁴ g₂(L)`, `g₃(L') = c⁻⁶ g₃(L)`, the discriminant
`Δ = g₂³ - 27 g₃²` scales by `c⁻¹²`, and `1728 g₂³ / Δ` is unchanged. With
`PeriodPair.exists_isHomothetic_ofTau` (every period pair is homothetic to `(1, τ)` for some `τ`
in the upper half-plane) and `PeriodPair.isHomothetic_ofTau_iff` (when `(1, τ)` and `(1, τ')` are
homothetic), this gives the three statements of Milne's Chapter III, §1–§3 used in the complex
uniformization of elliptic curves.

## Main results

* `PeriodPair.G_eq_of_lattice_eq_smul`, `PeriodPair.g₂_eq_of_lattice_eq_smul`,
  `PeriodPair.g₃_eq_of_lattice_eq_smul`, `PeriodPair.discriminant_eq_of_lattice_eq_smul`,
  `PeriodPair.jInvariant_eq_of_lattice_eq_smul`: scaling of the invariants.
* `PeriodPair.lattice_scale`: the lattice of `L.scale α` is `α` times the lattice of `L`.
* `PeriodPair.homothety_classes`: the three statements together, the second from
  `PeriodPair.exists_isHomothetic_ofTau` and `PeriodPair.IsHomothetic.symm`.
-/

@[expose] public section

open scoped Pointwise UpperHalfPlane MatrixGroups

namespace PeriodPair

/-- Multiplication by `c` as a bijection from the lattice of `L` onto the lattice of `L'`, when
the lattice of `L'` is `c` times the lattice of `L` with `c ≠ 0`. -/
noncomputable def latticeSmulEquiv {L L' : PeriodPair} {c : ℂ} (hc : c ≠ 0)
    (h : (L'.lattice : Set ℂ) = c • (L.lattice : Set ℂ)) : L.lattice ≃ L'.lattice where
  toFun x := ⟨c * x, by
    change c * (x : ℂ) ∈ (L'.lattice : Set ℂ)
    rw [h]
    exact Set.smul_mem_smul_set x.2⟩
  invFun y := ⟨c⁻¹ * y, by
    have hy : (y : ℂ) ∈ c • (L.lattice : Set ℂ) := h ▸ y.2
    obtain ⟨x, hx, hxy⟩ := Set.mem_smul_set.mp hy
    rw [← hxy, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    exact hx⟩
  left_inv x := by ext; simp [← mul_assoc, inv_mul_cancel₀ hc]
  right_inv y := by ext; simp [← mul_assoc, mul_inv_cancel₀ hc]

/-- **The Eisenstein sums of homothetic lattices.** Let $L$ and $L'$ be period pairs with
lattices $\Lambda$ and $\Lambda'$, and let $c \ne 0$ be a complex number with
$\Lambda' = c\Lambda$. Then for $n \ge 3$,
$G_n(L') = c^{-n} G_n(L)$, where $G_n(L) = \sum_{l \in \Lambda} l^{-n}$ (with $0^{-1} = 0$). The
Lean statement holds for every $n$: for $n \le 2$ the series diverges and both sides are $0$ by
the `tsum` convention.

Source: J. S. Milne, *Elliptic Curves*, 2nd ed., World Scientific, 2021, Chapter III, §2,
p. 89 ($G_{2k}(c\Lambda) = c^{-2k} G_{2k}(\Lambda)$). -/
theorem G_eq_of_lattice_eq_smul {L L' : PeriodPair} {c : ℂ} (hc : c ≠ 0)
    (h : (L'.lattice : Set ℂ) = c • (L.lattice : Set ℂ)) (n : ℕ) :
    L'.G n = c⁻¹ ^ n * L.G n := by
  rw [G, G, ← (latticeSmulEquiv hc h).tsum_eq, ← tsum_mul_left]
  congr 1 with x
  simp only [latticeSmulEquiv, Equiv.coe_fn_mk, mul_pow, mul_inv, inv_pow]

/-- **The invariant $g_2$ of homothetic lattices.** If the lattices of the period pairs $L$ and
$L'$ satisfy $\Lambda' = c\Lambda$ with $c \ne 0$, then $g_2(L') = c^{-4} g_2(L)$.

Source: J. S. Milne, *Elliptic Curves*, 2nd ed., World Scientific, 2021, Chapter III, §3, proof
of Theorem 3.10, p. 96 ($g_4(c\Lambda) = c^{-4} g_4(\Lambda)$, Milne's $g_4$ being $g_2$). -/
theorem g₂_eq_of_lattice_eq_smul {L L' : PeriodPair} {c : ℂ} (hc : c ≠ 0)
    (h : (L'.lattice : Set ℂ) = c • (L.lattice : Set ℂ)) :
    L'.g₂ = c⁻¹ ^ 4 * L.g₂ := by
  rw [g₂, g₂, G_eq_of_lattice_eq_smul hc h]
  ring

/-- **The invariant $g_3$ of homothetic lattices.** If the lattices of the period pairs $L$ and
$L'$ satisfy $\Lambda' = c\Lambda$ with $c \ne 0$, then $g_3(L') = c^{-6} g_3(L)$.

Source: J. S. Milne, *Elliptic Curves*, 2nd ed., World Scientific, 2021, Chapter III, §3, proof
of Theorem 3.10, p. 96 ($g_6(c\Lambda) = c^{-6} g_6(\Lambda)$, Milne's $g_6$ being $g_3$). -/
theorem g₃_eq_of_lattice_eq_smul {L L' : PeriodPair} {c : ℂ} (hc : c ≠ 0)
    (h : (L'.lattice : Set ℂ) = c • (L.lattice : Set ℂ)) :
    L'.g₃ = c⁻¹ ^ 6 * L.g₃ := by
  rw [g₃, g₃, G_eq_of_lattice_eq_smul hc h]
  ring

/-- **The discriminant of homothetic lattices.** If the lattices of the period pairs $L$ and $L'$
satisfy $\Lambda' = c\Lambda$ with $c \ne 0$, then
$g_2(L')^3 - 27 g_3(L')^2 = c^{-12} \bigl(g_2(L)^3 - 27 g_3(L)^2\bigr)$.

Source: J. S. Milne, *Elliptic Curves*, 2nd ed., World Scientific, 2021, Chapter III, §3, proof
of Theorem 3.10, p. 96. -/
theorem discriminant_eq_of_lattice_eq_smul {L L' : PeriodPair} {c : ℂ} (hc : c ≠ 0)
    (h : (L'.lattice : Set ℂ) = c • (L.lattice : Set ℂ)) :
    L'.g₂ ^ 3 - 27 * L'.g₃ ^ 2 = c⁻¹ ^ 12 * (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) := by
  rw [g₂_eq_of_lattice_eq_smul hc h, g₃_eq_of_lattice_eq_smul hc h]
  ring

/-- **The quotient $1728 g_2^3 / \Delta$ of homothetic lattices.** If the lattices of the period
pairs $L$ and $L'$ satisfy $\Lambda' = c\Lambda$ with $c \ne 0$, then, with
$\Delta = g_2^3 - 27 g_3^2$,
$1728\, g_2(L')^3 / \Delta(L') = 1728\, g_2(L)^3 / \Delta(L)$.

The statement needs no hypothesis $\Delta(L) \ne 0$: if $\Delta(L) = 0$, then $\Delta(L') = 0$ and
both sides are $0$ under Lean's convention $x / 0 = 0$.

Source: J. S. Milne, *Elliptic Curves*, 2nd ed., World Scientific, 2021, Chapter III, §3, proof
of Theorem 3.10, p. 96. -/
theorem jInvariant_eq_of_lattice_eq_smul {L L' : PeriodPair} {c : ℂ} (hc : c ≠ 0)
    (h : (L'.lattice : Set ℂ) = c • (L.lattice : Set ℂ)) :
    1728 * L'.g₂ ^ 3 / (L'.g₂ ^ 3 - 27 * L'.g₃ ^ 2) =
      1728 * L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) := by
  rw [discriminant_eq_of_lattice_eq_smul hc h, g₂_eq_of_lattice_eq_smul hc h]
  have hc12 : c⁻¹ ^ 12 ≠ 0 := pow_ne_zero _ (inv_ne_zero hc)
  rw [show 1728 * (c⁻¹ ^ 4 * L.g₂) ^ 3 = c⁻¹ ^ 12 * (1728 * L.g₂ ^ 3) by ring,
    mul_div_mul_left _ _ hc12]

/-- **The lattice of a scaled period pair.** For a period pair $L$ and
$\alpha \in \mathbb{C}^\times$, the lattice of `L.scale α` $= (\alpha\omega_1, \alpha\omega_2)$
is $\alpha$ times the lattice of $L$. -/
theorem lattice_scale (L : PeriodPair) (α : ℂˣ) :
    ((L.scale α).lattice : Set ℂ) = (α : ℂ) • (L.lattice : Set ℂ) := by
  ext z
  simp only [SetLike.mem_coe, mem_lattice, Set.mem_smul_set, scale_ω₁, scale_ω₂, smul_eq_mul]
  constructor
  · rintro ⟨m, n, rfl⟩
    exact ⟨_, ⟨m, n, rfl⟩, by ring⟩
  · rintro ⟨_, ⟨m, n, rfl⟩, rfl⟩
    exact ⟨m, n, by ring⟩

/-- **Homothety classes of period pairs and the modular group.** For period pairs, with
$\Delta = g_2^3 - 27 g_3^2$:

1. if the lattices of $L$ and $L'$ satisfy $\Lambda' = c\Lambda$ with $c \ne 0$, then
   $g_2(L') = c^{-4} g_2(L)$, $g_3(L') = c^{-6} g_3(L)$, $\Delta(L') = c^{-12}\Delta(L)$ and
   $1728\, g_2(L')^3 / \Delta(L') = 1728\, g_2(L)^3 / \Delta(L)$ (with $x / 0 = 0$, so no
   hypothesis $\Delta(L) \ne 0$ is needed);
2. every period pair is homothetic to $(1, \tau)$ for some $\tau$ in the upper half-plane;
3. for $\tau, \tau' \in \mathbb{H}$, the period pairs $(1, \tau)$ and $(1, \tau')$ are homothetic
   if and only if $\tau' = \gamma\tau$ for some $\gamma \in \mathrm{SL}_2(\mathbb{Z})$
   (`PeriodPair.isHomothetic_ofTau_iff`).

Source: J. S. Milne, *Elliptic Curves*, 2nd ed., World Scientific, 2021, Chapter III, §1,
Proposition 1.1 and the bijection (20), pp. 85–86; §2, p. 89; §3, proof of Theorem 3.10,
p. 96. -/
theorem homothety_classes :
    (∀ (L L' : PeriodPair) (c : ℂ), c ≠ 0 → (L'.lattice : Set ℂ) = c • (L.lattice : Set ℂ) →
      L'.g₂ = c⁻¹ ^ 4 * L.g₂ ∧ L'.g₃ = c⁻¹ ^ 6 * L.g₃ ∧
      L'.g₂ ^ 3 - 27 * L'.g₃ ^ 2 = c⁻¹ ^ 12 * (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) ∧
      1728 * L'.g₂ ^ 3 / (L'.g₂ ^ 3 - 27 * L'.g₃ ^ 2) =
        1728 * L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) ∧
    (∀ L : PeriodPair, ∃ τ : ℍ, L.IsHomothetic (ofTau τ τ.im_pos.ne')) ∧
    (∀ τ τ' : ℍ, (ofTau τ τ.im_pos.ne').IsHomothetic (ofTau τ' τ'.im_pos.ne') ↔
      ∃ γ : SL(2, ℤ), τ' = γ • τ) :=
  ⟨fun _ _ _ hc h ↦ ⟨g₂_eq_of_lattice_eq_smul hc h, g₃_eq_of_lattice_eq_smul hc h,
      discriminant_eq_of_lattice_eq_smul hc h, jInvariant_eq_of_lattice_eq_smul hc h⟩,
    fun L ↦ (exists_isHomothetic_ofTau L).imp fun _ h ↦ h.symm, isHomothetic_ofTau_iff⟩

end PeriodPair
