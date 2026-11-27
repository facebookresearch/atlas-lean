/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Totient
public import MathlibExt.NumberTheory.ImaginaryQuadraticDiscriminant
public import MathlibExt.NumberTheory.QuadraticForms.GaussClassNumber
public import MathlibExt.NumberTheory.QuadraticForms.RootLattice
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Totient lower bounds for Gauss class numbers

For a negative fundamental discriminant $D$ and an integer $f \ge 1$, the Gauss class numbers
satisfy $h(D)\,\varphi(f) \le h(f^2 D)$ when $D \notin \{-3, -4\}$ and
$\varphi(f) \le 3\, h(f^2 D)$ when $D \in \{-3, -4\}$.

The argument is elementary. Reduction theory identifies $h(d)$ with the number of proper
equivalence classes of primitive positive definite forms of discriminant $d$. For a form $F$ of
discriminant $D$ and an integer $k$ with $\gcd(F(1, k), f) = 1$, the form
$F(x, kx + fy)$ is primitive of discriminant $f^2 D$. After moving $F$ within its class, every
$k$ prime to $f$ qualifies, and two such forms are properly equivalent only if their forms $F$
are, and then, up to an automorph of $F$, only if the two values of $k$ agree modulo $f$.

The reduction theory is public: by `GaussClassNumberTotient.exists_reduced` and
`GaussClassNumberTotient.eq_of_equiv_of_reduced`, each positive definite form is properly
equivalent (`BinaryQuadraticForm.ProperlyEquivalent`) to exactly one Gauss-reduced form. The
proofs here work with the coefficient relation `FormEquiv`, which `properlyEquivalent_iff_formEquiv`
identifies with `BinaryQuadraticForm.ProperlyEquivalent`.
-/

namespace MetaMathlibExt

namespace GaussClassNumberTotient

open BinaryQuadraticForm

/-- The form `F(px + qy, rx + sy)`, for `F = (a, b, c)` standing for `ax² + bxy + cy²`. -/
def act (F : ℤ × ℤ × ℤ) (p q r s : ℤ) : ℤ × ℤ × ℤ :=
  (F.1 * p ^ 2 + F.2.1 * p * r + F.2.2 * r ^ 2,
    2 * F.1 * p * q + F.2.1 * (p * s + q * r) + 2 * F.2.2 * r * s,
    F.1 * q ^ 2 + F.2.1 * q * s + F.2.2 * s ^ 2)

/-- The value `F(x, y) = ax² + bxy + cy²` of `F = (a, b, c)`. -/
def val (F : ℤ × ℤ × ℤ) (x y : ℤ) : ℤ := F.1 * x ^ 2 + F.2.1 * x * y + F.2.2 * y ^ 2

/-- The discriminant `b² - 4ac` of `F = (a, b, c)`. -/
def disc (F : ℤ × ℤ × ℤ) : ℤ := discrim F.1 F.2.1 F.2.2

theorem act_act (F : ℤ × ℤ × ℤ) (p q r s p' q' r' s' : ℤ) :
    act (act F p q r s) p' q' r' s' =
      act F (p * p' + q * r') (p * q' + q * s') (r * p' + s * r') (r * q' + s * s') := by
  simp only [act, Prod.mk.injEq]
  refine ⟨by ring, by ring, by ring⟩

theorem act_one (F : ℤ × ℤ × ℤ) : act F 1 0 0 1 = F := by
  obtain ⟨a, b, c⟩ := F
  simp only [act, Prod.mk.injEq]
  refine ⟨by ring, by ring, by ring⟩

theorem disc_act (F : ℤ × ℤ × ℤ) (p q r s : ℤ) :
    disc (act F p q r s) = (p * s - q * r) ^ 2 * disc F := by
  simp only [disc, act, discrim]
  ring

theorem val_act (F : ℤ × ℤ × ℤ) (p q r s x y : ℤ) :
    val (act F p q r s) x y = val F (p * x + q * y) (r * x + s * y) := by
  simp only [val, act]
  ring

/-- Proper equivalence: `G = F(px + qy, rx + sy)` with `ps - qr = 1`. -/
def FormEquiv (F G : ℤ × ℤ × ℤ) : Prop :=
  ∃ p q r s : ℤ, p * s - q * r = 1 ∧ act F p q r s = G

theorem FormEquiv.refl (F : ℤ × ℤ × ℤ) : FormEquiv F F := ⟨1, 0, 0, 1, by ring, act_one F⟩

theorem FormEquiv.trans {F G H : ℤ × ℤ × ℤ} (h₁ : FormEquiv F G) (h₂ : FormEquiv G H) :
    FormEquiv F H := by
  obtain ⟨p, q, r, s, hd, rfl⟩ := h₁
  obtain ⟨p', q', r', s', hd', rfl⟩ := h₂
  refine ⟨_, _, _, _, ?_, (act_act F p q r s p' q' r' s').symm⟩
  linear_combination (p' * s' - q' * r') * hd + hd'

theorem FormEquiv.symm {F G : ℤ × ℤ × ℤ} (h : FormEquiv F G) : FormEquiv G F := by
  obtain ⟨p, q, r, s, hd, rfl⟩ := h
  refine ⟨s, -q, -r, p, by linear_combination hd, ?_⟩
  rw [act_act]
  obtain ⟨a, b, c⟩ := F
  simp only [act, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (a * (p * s - q * r + 1)) * hd
  · linear_combination (b * (p * s - q * r + 1)) * hd
  · linear_combination (c * (p * s - q * r + 1)) * hd

theorem FormEquiv.disc_eq {F G : ℤ × ℤ × ℤ} (h : FormEquiv F G) : disc G = disc F := by
  obtain ⟨p, q, r, s, hd, rfl⟩ := h
  rw [disc_act, hd]; ring

/-- `FormEquiv` is `BinaryQuadraticForm.ProperlyEquivalent`, with the entries of the matrix in
`SL(2, ℤ)` as its witnesses: `BinaryQuadraticForm.substitute F γ` is
`act F (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)`. -/
theorem properlyEquivalent_iff_formEquiv (F G : ℤ × ℤ × ℤ) :
    ProperlyEquivalent F G ↔ FormEquiv F G := by
  constructor
  · rintro ⟨γ, rfl⟩
    refine ⟨γ 0 0, γ 0 1, γ 1 0, γ 1 1, ?_, rfl⟩
    have := γ.det_coe
    rwa [Matrix.det_fin_two] at this
  · rintro ⟨p, q, r, s, hdet, rfl⟩
    exact ⟨⟨!![p, q; r, s], by rw [Matrix.det_fin_two_of]; exact hdet⟩, rfl⟩

theorem c_pos_of {a b c : ℤ} (ha : 0 < a) (hd : discrim a b c < 0) : 0 < c := by
  unfold discrim at hd; nlinarith [sq_nonneg b]

theorem IsGaussReduced.b_gt {a b c : ℤ} (h : IsGaussReduced a b c) : -a < b := by
  rcases lt_or_eq_of_le h.neg_le with h1 | h1
  · exact h1
  · have := h.boundary (Or.inl (by rw [← h1, abs_neg, abs_of_pos h.pos]))
    linarith [h.pos]

theorem exists_reduced_aux (n : ℕ) : ∀ F : ℤ × ℤ × ℤ, F.1.toNat = n → 0 < F.1 → disc F < 0 →
    ∃ G, FormEquiv F G ∧ IsGaussReduced G.1 G.2.1 G.2.2 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro F hn ha hd
  obtain ⟨a, b, c⟩ := F
  simp only at hn ha hd
  have h2a : 0 < 2 * a := by linarith
  have hmod := Int.mul_ediv_add_emod (a - b) (2 * a)
  have hr0 := Int.emod_nonneg (a - b) (ne_of_gt h2a)
  have hr1 := Int.emod_lt_of_pos (a - b) h2a
  set k := (a - b) / (2 * a) with hk
  have hF₁ : act (a, b, c) 1 k 0 1 = (a, 2 * a * k + b, a * k ^ 2 + b * k + c) := by
    simp only [act, Prod.mk.injEq]; refine ⟨by ring, by ring, by ring⟩
  have hE₁ : FormEquiv (a, b, c) (a, 2 * a * k + b, a * k ^ 2 + b * k + c) :=
    ⟨1, k, 0, 1, by ring, hF₁⟩
  set b₁ := 2 * a * k + b with hb₁
  set c₁ := a * k ^ 2 + b * k + c with hc₁
  have hd₁ : disc (a, b₁, c₁) < 0 := by rw [hE₁.disc_eq]; exact hd
  have hb₁lo : -a < b₁ := by linarith
  have hb₁hi : b₁ ≤ a := by linarith
  have hc₁pos : 0 < c₁ := c_pos_of ha hd₁
  have hF₂ : act (a, b₁, c₁) 0 (-1) 1 0 = (c₁, -b₁, a) := by
    simp only [act, Prod.mk.injEq]; refine ⟨by ring, by ring, by ring⟩
  have hE₂ : FormEquiv (a, b₁, c₁) (c₁, -b₁, a) := ⟨0, -1, 1, 0, by ring, hF₂⟩
  by_cases hlt : c₁ < a
  · obtain ⟨G, hG, hred⟩ := ih c₁.toNat (by omega) (c₁, -b₁, a) rfl hc₁pos
      (by rw [hE₂.disc_eq]; exact hd₁)
    exact ⟨G, hE₁.trans (hE₂.trans hG), hred⟩
  · push Not at hlt
    by_cases hbd : a = c₁ ∧ b₁ < 0
    · refine ⟨(c₁, -b₁, a), hE₁.trans hE₂, ?_⟩
      have hd₂ : disc (c₁, -b₁, a) < 0 := by rw [hE₂.disc_eq]; exact hd₁
      refine ⟨hc₁pos, hd₂, ?_, by simp only; linarith [hbd.1], ?_⟩
      · simp only; rw [abs_of_pos (by linarith [hbd.2])]; linarith [hbd.1]
      · intro _; simp only; linarith [hbd.2]
    · refine ⟨(a, b₁, c₁), hE₁, ha, hd₁, abs_le.mpr ⟨by linarith, hb₁hi⟩, hlt, ?_⟩
      simp only
      rintro (h | h)
      · by_contra hneg
        push Not at hneg
        rw [abs_of_neg hneg] at h
        linarith
      · by_contra hneg
        push Not at hneg
        exact hbd ⟨h, hneg⟩

/-- `exists_reduced` for the coefficient relation `FormEquiv`. -/
theorem exists_formEquiv_reduced (F : ℤ × ℤ × ℤ) (ha : 0 < F.1) (hd : disc F < 0) :
    ∃ G, FormEquiv F G ∧ IsGaussReduced G.1 G.2.1 G.2.2 :=
  exists_reduced_aux _ F rfl ha hd

/-- **Every positive definite binary quadratic form is properly equivalent to a reduced form.**
Let $F = a x^2 + b x y + c y^2$ be an integral binary quadratic form with $a > 0$ and negative
discriminant $b^2 - 4ac$. Then $F$ is properly equivalent (`BinaryQuadraticForm.ProperlyEquivalent`:
$G(x, y) = F(px + qy, rx + sy)$ for some
$\begin{pmatrix} p & q \\ r & s \end{pmatrix} \in \mathrm{SL}_2(\mathbb{Z})$) to a Gauss-reduced
form $G = A x^2 + B x y + C y^2$ (`BinaryQuadraticForm.IsGaussReduced`): $A > 0$,
$B^2 - 4AC < 0$, $|B| \le A \le C$, and $B \ge 0$ whenever $|B| = A$ or $A = C$.

Source: Leonard Eugene Dickson, *Introduction to the Theory of Numbers*, University of Chicago
Press, 1929, Chapter V, §40, Theorem 51, p. 68: "Every real, positive form $q$ is equivalent to
a reduced form." This is its case of integral forms. There, a form is positive when its
discriminant is negative and $a > 0$ (p. 67), equivalence is by integral transformations of
determinant $1$ (§39, pp. 65–66), and a positive form is reduced when $-a < b \le a$, $c \ge a$,
with $b \ge 0$ if $c = a$ (his (18), p. 68); so the reduced positive forms are exactly the
Gauss-reduced forms. -/
public theorem exists_reduced (F : ℤ × ℤ × ℤ) (ha : 0 < F.1)
    (hd : discrim F.1 F.2.1 F.2.2 < 0) :
    ∃ G, ProperlyEquivalent F G ∧ IsGaussReduced G.1 G.2.1 G.2.2 := by
  obtain ⟨G, hG, hred⟩ := exists_formEquiv_reduced F ha hd
  exact ⟨G, (properlyEquivalent_iff_formEquiv F G).2 hG, hred⟩

theorem one_le_sq_of_ne {x : ℤ} (hx : x ≠ 0) : 1 ≤ x ^ 2 := by
  have := sq_pos_of_ne_zero hx
  omega

theorem val_ge_of_reduced_of_ne {a b c : ℤ} (h : IsGaussReduced a b c) {x y : ℤ} (hx : x ≠ 0)
    (hy : y ≠ 0) : a - |b| + c ≤ val (a, b, c) x y := by
  simp only [val]
  have hb := h.abs_le
  have hac := h.le
  have ha := h.pos
  have h1 : -(|b| * (|x| * |y|)) ≤ b * x * y := by
    have := neg_abs_le (b * x * y)
    rw [abs_mul, abs_mul] at this
    linarith
  have hx2 := one_le_sq_of_ne hx
  have hy2 := one_le_sq_of_ne hy
  have hax : |x| ^ 2 = x ^ 2 := sq_abs x
  have hay : |y| ^ 2 = y ^ 2 := sq_abs y
  have hbn : 0 ≤ |b| := abs_nonneg b
  rcases le_total |y| |x| with hle | hle
  · have e1 : |b| * (|x| * |y|) ≤ |b| * x ^ 2 := by
      rw [← hax]
      exact mul_le_mul_of_nonneg_left (by nlinarith [abs_nonneg x, abs_nonneg y]) hbn
    have e2 : y ^ 2 ≤ x ^ 2 := by rw [← hax, ← hay]; nlinarith [abs_nonneg x, abs_nonneg y]
    nlinarith
  · have e1 : |b| * (|x| * |y|) ≤ |b| * y ^ 2 := by
      rw [← hay]
      exact mul_le_mul_of_nonneg_left (by nlinarith [abs_nonneg x, abs_nonneg y]) hbn
    have e2 : x ^ 2 ≤ y ^ 2 := by rw [← hax, ← hay]; nlinarith [abs_nonneg x, abs_nonneg y]
    nlinarith

theorem val_ge_of_reduced {a b c : ℤ} (h : IsGaussReduced a b c) {x y : ℤ}
    (hxy : x ≠ 0 ∨ y ≠ 0) : a ≤ val (a, b, c) x y := by
  have hb := h.abs_le
  have hac := h.le
  have ha := h.pos
  by_cases hx : x = 0
  · have hy : y ≠ 0 := hxy.resolve_left (not_not.mpr hx)
    subst hx
    simp only [val]
    nlinarith [one_le_sq_of_ne hy]
  · by_cases hy : y = 0
    · subst hy
      simp only [val]
      nlinarith [one_le_sq_of_ne hx]
    · have := val_ge_of_reduced_of_ne h hx hy
      linarith

/-- `eq_of_equiv_of_reduced` for the coefficient relation `FormEquiv`. -/
theorem eq_of_formEquiv_of_reduced {F G : ℤ × ℤ × ℤ} (hF : IsGaussReduced F.1 F.2.1 F.2.2)
    (hG : IsGaussReduced G.1 G.2.1 G.2.2) (h : FormEquiv F G) : F = G := by
  have hdisc : disc G = disc F := h.disc_eq
  obtain ⟨a, b, c⟩ := F
  obtain ⟨a', b', c'⟩ := G
  simp only at hF hG
  obtain ⟨p, q, r, s, hdet, hact⟩ := h
  have hval1 : a' = val (a, b, c) p r := by
    have := congrArg Prod.fst hact; simp only [act, val] at this ⊢; linarith
  have hval2 : b' = 2 * a * p * q + b * (p * s + q * r) + 2 * c * r * s := by
    have := congrArg (fun x => x.2.1) hact; simp only [act] at this; linarith
  have hsymm : FormEquiv (a', b', c') (a, b, c) := FormEquiv.symm ⟨p, q, r, s, hdet, hact⟩
  have ha := hF.pos
  have ha' := hG.pos
  have hb := hF.abs_le
  have hb' := hG.abs_le
  have hac := hF.le
  have hac' := hG.le
  have hblo := IsGaussReduced.b_gt hF
  have hblo' := IsGaussReduced.b_gt hG
  have hbhi := hF.le_of_abs_le
  have hbhi' := hG.le_of_abs_le
  simp only [disc, discrim] at hdisc
  -- a' ≥ a
  have hpr : p ≠ 0 ∨ r ≠ 0 := by
    by_contra hc; push Not at hc; rw [hc.1, hc.2] at hdet; simp at hdet
  have h1 : a ≤ a' := hval1 ▸ val_ge_of_reduced hF hpr
  -- a ≥ a'
  have h2 : a' ≤ a := by
    obtain ⟨p', q', r', s', hdet', hact'⟩ := hsymm
    have hv : a = val (a', b', c') p' r' := by
      have := congrArg Prod.fst hact'; simp only [act, val] at this ⊢; linarith
    have hpr' : p' ≠ 0 ∨ r' ≠ 0 := by
      by_contra hc; push Not at hc; rw [hc.1, hc.2] at hdet'; simp at hdet'
    exact hv ▸ val_ge_of_reduced hG hpr'
  have haa : a' = a := le_antisymm h2 h1
  subst haa
  -- c' from b'
  have hc_of_b : b' = b → c' = c := by
    intro hbb; subst hbb
    have : 4 * a' * (c' - c) = 0 := by linarith
    have h4 : (4 * a') ≠ 0 := by positivity
    have := (mul_eq_zero.mp this).resolve_left h4
    linarith
  suffices hbb : b' = b by rw [hbb, hc_of_b hbb]
  by_cases hr : r = 0
  · subst hr
    have hps : p * s = 1 := by linarith
    have hb2 : b' = b + 2 * a' * (p * q) := by
      rw [hval2, show p * s + q * 0 = 1 by linarith]; ring
    have hm1 : p * q < 1 := by
      by_contra hc; push Not at hc; nlinarith
    have hm2 : -1 < p * q := by
      by_contra hc; push Not at hc; nlinarith
    have : p * q = 0 := by omega
    rw [hb2, this]; ring
  · by_cases hp : p = 0
    · subst hp
      have hqr : q * r = -1 := by linarith
      have hv : a' = c * r ^ 2 := by rw [hval1]; simp only [val]; ring
      have hr2 := one_le_sq_of_ne hr
      have hca : c = a' := by nlinarith
      have hb2 : b' = -b + 2 * a' * (r * s) := by
        rw [hval2, hca.symm]; rw [show 0 * s + q * r = -1 by linarith]; ring
      have hb0 : 0 ≤ b := hF.boundary (Or.inr hca.symm)
      have hm1 : r * s ≤ 1 := by
        by_contra hc; push Not at hc; nlinarith
      have hm2 : 0 ≤ r * s := by
        by_contra hc; push Not at hc; nlinarith
      rcases (show r * s = 0 ∨ r * s = 1 by omega) with hm | hm
      · rw [hm] at hb2
        have hcc : c' = c := by
          have : 4 * a' * (c' - c) = 0 := by rw [hb2] at hdisc; nlinarith
          have h4 : (4 * a') ≠ 0 := by positivity
          have := (mul_eq_zero.mp this).resolve_left h4
          linarith
        have hb'0 : 0 ≤ b' := hG.boundary (Or.inr (by rw [hcc, hca]))
        linarith
      · rw [hm] at hb2
        linarith
    · have hge := val_ge_of_reduced_of_ne hF hp hr
      rw [← hval1] at hge
      have hbab : |b| = a' := by linarith
      have hca : c = a' := by linarith
      have hb0 : 0 ≤ b := hF.boundary (Or.inl hbab)
      have hbeq : b = a' := by rw [abs_of_nonneg hb0] at hbab; exact hbab
      -- G = (a', b', c') with b'^2 - 4 a' c' = -3 a'^2
      have hc'le : c' ≤ a' := by
        have hsq : b' ^ 2 ≤ a' ^ 2 := by
          have := sq_le_sq' (abs_le.mp hb').1 (abs_le.mp hb').2
          simpa using this
        rw [hbeq, hca] at hdisc
        nlinarith
      have hcc : c' = a' := le_antisymm hc'le hac'
      have hb'0 : 0 ≤ b' := hG.boundary (Or.inr hcc.symm)
      rw [hbeq, hca, hcc] at hdisc
      have : b' ^ 2 = a' ^ 2 := by linarith
      have := (sq_eq_sq₀ hb'0 ha'.le).mp this
      rw [this, hbeq]

/-- **Properly equivalent reduced forms are equal.** If two integral binary quadratic forms
$F$ and $G$ are Gauss reduced (`BinaryQuadraticForm.IsGaussReduced`) and $F$ is properly
equivalent to $G$ (`BinaryQuadraticForm.ProperlyEquivalent`), then $F = G$.

Source: Leonard Eugene Dickson, *Introduction to the Theory of Numbers*, University of Chicago
Press, 1929, Chapter V, §42, Theorem 53, p. 71: "Equivalent, positive, reduced forms are
identical." This is its case of integral forms, with positive forms, equivalence and reduced
forms as recalled at `exists_reduced`; Dickson derives it from his Theorem 52, p. 70. -/
public theorem eq_of_equiv_of_reduced {F G : ℤ × ℤ × ℤ} (hF : IsGaussReduced F.1 F.2.1 F.2.2)
    (hG : IsGaussReduced G.1 G.2.1 G.2.2) (h : ProperlyEquivalent F G) : F = G :=
  eq_of_formEquiv_of_reduced hF hG ((properlyEquivalent_iff_formEquiv F G).1 h)

theorem act_inv {F : ℤ × ℤ × ℤ} {p q r s : ℤ} (hdet : p * s - q * r = 1) :
    act (act F p q r s) s (-q) (-r) p = F := by
  rw [act_act]
  obtain ⟨a, b, c⟩ := F
  simp only [act, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (a * (p * s - q * r + 1)) * hdet
  · linear_combination (b * (p * s - q * r + 1)) * hdet
  · linear_combination (c * (p * s - q * r + 1)) * hdet

/-- The content `gcd(a, b, c)` of `F = (a, b, c)`. -/
def cont (F : ℤ × ℤ × ℤ) : ℕ := Int.gcd (Int.gcd F.1 F.2.1 : ℤ) F.2.2

theorem dvd_cont_iff {F : ℤ × ℤ × ℤ} {d : ℤ} :
    d ∣ (cont F : ℤ) ↔ d ∣ F.1 ∧ d ∣ F.2.1 ∧ d ∣ F.2.2 := by
  constructor
  · intro h
    have h1 : (cont F : ℤ) ∣ (Int.gcd F.1 F.2.1 : ℤ) := Int.gcd_dvd_left _ _
    have h2 : (Int.gcd F.1 F.2.1 : ℤ) ∣ F.1 := Int.gcd_dvd_left _ _
    have h3 : (Int.gcd F.1 F.2.1 : ℤ) ∣ F.2.1 := Int.gcd_dvd_right _ _
    have h4 : (cont F : ℤ) ∣ F.2.2 := Int.gcd_dvd_right _ _
    exact ⟨h.trans (h1.trans h2), h.trans (h1.trans h3), h.trans h4⟩
  · rintro ⟨h1, h2, h3⟩
    exact Int.dvd_coe_gcd (Int.dvd_coe_gcd h1 h2) h3

theorem dvd_act {F : ℤ × ℤ × ℤ} {d : ℤ} (h : d ∣ F.1 ∧ d ∣ F.2.1 ∧ d ∣ F.2.2) (p q r s : ℤ) :
    d ∣ (act F p q r s).1 ∧ d ∣ (act F p q r s).2.1 ∧ d ∣ (act F p q r s).2.2 := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [act]
  exact ⟨dvd_add (dvd_add (h1.mul_right _) ((h2.mul_right _).mul_right _)) (h3.mul_right _),
    dvd_add (dvd_add (((h1.mul_left 2).mul_right p).mul_right q) (h2.mul_right _))
      (((h3.mul_left 2).mul_right r).mul_right s),
    dvd_add (dvd_add (h1.mul_right _) ((h2.mul_right _).mul_right _)) (h3.mul_right _)⟩

theorem cont_act {F : ℤ × ℤ × ℤ} {p q r s : ℤ} (hdet : p * s - q * r = 1) :
    cont (act F p q r s) = cont F := by
  have h1 : (cont F : ℤ) ∣ (cont (act F p q r s) : ℤ) :=
    dvd_cont_iff.mpr (dvd_act (dvd_cont_iff.mp dvd_rfl) p q r s)
  have h2 : (cont (act F p q r s) : ℤ) ∣ (cont F : ℤ) := by
    have := dvd_act (dvd_cont_iff.mp (dvd_refl (cont (act F p q r s) : ℤ))) s (-q) (-r) p
    rw [act_inv hdet] at this
    exact dvd_cont_iff.mpr this
  exact Nat.dvd_antisymm (Int.natCast_dvd_natCast.mp h2) (Int.natCast_dvd_natCast.mp h1)

theorem FormEquiv.cont_eq {F G : ℤ × ℤ × ℤ} (h : FormEquiv F G) : cont G = cont F := by
  obtain ⟨p, q, r, s, hd, rfl⟩ := h
  exact cont_act hd

/-- The form `F(x, kx + fy)`, of discriminant `f² disc F`. -/
def lift (F : ℤ × ℤ × ℤ) (k f : ℤ) : ℤ × ℤ × ℤ := act F 1 0 k f

theorem lift_eq (F : ℤ × ℤ × ℤ) (k f : ℤ) :
    lift F k f = (val F 1 k, f * (F.2.1 + 2 * F.2.2 * k), F.2.2 * f ^ 2) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only [lift, act, val] <;> ring

theorem disc_lift (F : ℤ × ℤ × ℤ) (k f : ℤ) : disc (lift F k f) = f ^ 2 * disc F := by
  rw [lift, disc_act]; ring

theorem cont_lift {F : ℤ × ℤ × ℤ} {k f : ℤ} (hF : cont F = 1) (hcop : IsCoprime (val F 1 k) f) :
    cont (lift F k f) = 1 := by
  set d : ℤ := (cont (lift F k f) : ℤ) with hd
  have hdv := dvd_cont_iff.mp (dvd_refl d)
  rw [lift_eq] at hdv
  obtain ⟨hA, hB, hC⟩ := hdv
  simp only at hA hB hC
  have hdf : IsCoprime d f := hcop.of_isCoprime_of_dvd_left hA
  have hB' : d ∣ F.2.1 + 2 * F.2.2 * k := hdf.dvd_of_dvd_mul_left hB
  have hC' : d ∣ F.2.2 := (hdf.pow_right (n := 2)).dvd_of_dvd_mul_right hC
  have hb : d ∣ F.2.1 := by
    have := dvd_sub hB' ((hC'.mul_left 2).mul_right k)
    simpa using this
  have ha : d ∣ F.1 := by
    have h1 := dvd_sub (dvd_sub hA (hb.mul_right k)) (hC'.mul_right (k ^ 2))
    simp only [val] at h1
    have e : F.1 * 1 ^ 2 + F.2.1 * 1 * k + F.2.2 * k ^ 2 - F.2.1 * k - F.2.2 * k ^ 2 = F.1 := by
      ring
    rwa [e] at h1
  have h1 : d ∣ ((1 : ℕ) : ℤ) := hF ▸ dvd_cont_iff.mpr ⟨ha, hb, hC'⟩
  have : cont (lift F k f) ∣ 1 := Int.natCast_dvd_natCast.mp (by simpa [hd] using h1)
  exact Nat.dvd_one.mp this

theorem lift_inj {F F' : ℤ × ℤ × ℤ} {k f : ℤ} (hf : f ≠ 0) (h : lift F k f = lift F' k f) :
    F = F' := by
  rw [lift_eq, lift_eq] at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  have hf2 : f ^ 2 ≠ 0 := pow_ne_zero 2 hf
  have hc : F.2.2 = F'.2.2 := mul_right_cancel₀ hf2 h3
  have hb : F.2.1 = F'.2.1 := by
    have := mul_left_cancel₀ hf h2
    rw [hc] at this; linarith
  have ha : F.1 = F'.1 := by
    simp only [val] at h1; rw [hb, hc] at h1; linarith
  obtain ⟨a, b, c⟩ := F
  obtain ⟨a', b', c'⟩ := F'
  simp only at ha hb hc
  rw [ha, hb, hc]

theorem dvd_of_sq_dvd {A f β x : ℤ} (hf : f ≠ 0) (hcop : IsCoprime A f)
    (h : f ^ 2 ∣ A * β ^ 2 + f * x * β) : f ∣ β := by
  have hg : 0 < Int.gcd β f := Int.gcd_pos_of_ne_zero_right β hf
  obtain ⟨g, β', f', hg0, hgcd, hβ, hf'⟩ := Int.exists_gcd_one' hg
  have hgz : (g : ℤ) ≠ 0 := by exact_mod_cast hg0.ne'
  have h2 : f' ^ 2 ∣ A * β' ^ 2 + f' * x * β' := by
    have h' : f' ^ 2 * (g : ℤ) ^ 2 ∣ (A * β' ^ 2 + f' * x * β') * (g : ℤ) ^ 2 := by
      have e1 : f ^ 2 = f' ^ 2 * (g : ℤ) ^ 2 := by rw [hf']; ring
      have e2 : A * β ^ 2 + f * x * β = (A * β' ^ 2 + f' * x * β') * (g : ℤ) ^ 2 := by
        rw [hβ, hf']; ring
      rw [← e1, ← e2]; exact h
    exact (mul_dvd_mul_iff_right (pow_ne_zero 2 hgz)).mp h'
  have h3 : f' ∣ A * β' ^ 2 := by
    have h4 : f' ∣ A * β' ^ 2 + f' * x * β' := (dvd_pow_self f' two_ne_zero).trans h2
    have h5 : f' ∣ f' * x * β' := (dvd_mul_right f' x).mul_right β'
    have := dvd_sub h4 h5
    simpa using this
  have hcA : IsCoprime A f' := hcop.of_isCoprime_of_dvd_right ⟨g, by rw [hf']⟩
  have hcβ : IsCoprime β' f' := Int.isCoprime_iff_gcd_eq_one.mpr hgcd
  have hc : IsCoprime (A * β' ^ 2) f' := hcA.mul_left (hcβ.pow_left)
  have hu : IsUnit f' := hc.isUnit_of_dvd' h3 dvd_rfl
  rcases Int.isUnit_eq_one_or hu with h1 | h1
  · exact ⟨β', by rw [hβ, hf', h1]; ring⟩
  · exact ⟨-β', by rw [hβ, hf', h1]; ring⟩

theorem key {F₁ F₂ : ℤ × ℤ × ℤ} {f k₁ k₂ α β γ δ : ℤ} (hf : f ≠ 0) (hdet : α * δ - β * γ = 1)
    (hact : act (lift F₁ k₁ f) α β γ δ = lift F₂ k₂ f) (hcop : IsCoprime (val F₁ 1 k₁) f) :
    ∃ β₁, β = f * β₁ ∧
      act F₁ (α - β₁ * k₂) β₁ (k₁ * α + f * γ - k₁ * β₁ * k₂ - δ * k₂) (k₁ * β₁ + δ) = F₂ ∧
      (α - β₁ * k₂) * (k₁ * β₁ + δ) - β₁ * (k₁ * α + f * γ - k₁ * β₁ * k₂ - δ * k₂) = 1 := by
  have hc := congrArg (fun x => x.2.2) hact
  rw [lift_eq, lift_eq] at hc
  simp only [act] at hc
  have hdvd : f ^ 2 ∣ val F₁ 1 k₁ * β ^ 2 + f * ((F₁.2.1 + 2 * F₁.2.2 * k₁) * δ) * β := by
    refine ⟨F₂.2.2 - F₁.2.2 * δ ^ 2, ?_⟩
    linear_combination hc
  obtain ⟨β₁, hβ⟩ := dvd_of_sq_dvd hf hcop hdvd
  subst hβ
  refine ⟨β₁, rfl, ?_, by linear_combination hdet⟩
  apply lift_inj hf
  rw [← hact, lift, lift, act_act, act_act]
  congr 1 <;> ring

/-- Proper automorphs of a primitive form `(a, b, c)` have the shape
`[[(t - bu)/2, -cu], [au, (t + bu)/2]]` with `t² - Du² = 4`. -/
theorem automorph {F : ℤ × ℤ × ℤ} {p q r s : ℤ} (hcont : cont F = 1) (hdet : p * s - q * r = 1)
    (hact : act F p q r s = F) :
    ∃ u, r = F.1 * u ∧ q = -(F.2.2 * u) ∧ s = p + F.2.1 * u ∧
      (2 * p + F.2.1 * u) ^ 2 - disc F * u ^ 2 = 4 := by
  obtain ⟨a, b, c⟩ := F
  simp only at *
  have e1 := congrArg Prod.fst hact
  have e2 := congrArg (fun x => x.2.1) hact
  have e3 := congrArg (fun x => x.2.2) hact
  simp only [act] at e1 e2 e3
  -- commuting relations
  have R11 : a * q + c * r = 0 := by
    have : 2 * (a * q + c * r) = 0 := by
      linear_combination p * e2 - 2 * q * e1 - (b * p + 2 * c * r) * hdet
    linarith
  have R21 : a * (s - p) = b * r := by
    have : 2 * (a * (s - p) - b * r) = 0 := by
      linear_combination r * e2 - 2 * s * e1 + (2 * a * p + b * r) * hdet
    linarith
  have R12 : b * q = c * (p - s) := by
    have : 2 * (b * q - c * (p - s)) = 0 := by
      linear_combination (-q) * e2 + 2 * p * e3 - (b * q + 2 * c * s) * hdet
    linarith
  -- Bezout for gcd(gcd a b, c) = 1
  have hg1 : (Int.gcd (Int.gcd a b : ℤ) c : ℤ) = 1 := by
    simp only [cont] at hcont; exact_mod_cast hcont
  have bz1 := Int.gcd_eq_gcd_ab (Int.gcd a b : ℤ) c
  have bz2 := Int.gcd_eq_gcd_ab a b
  set x := Int.gcdA (Int.gcd a b : ℤ) c
  set z := Int.gcdB (Int.gcd a b : ℤ) c
  set x₁ := Int.gcdA a b
  set y₁ := Int.gcdB a b
  have hbez : a * (x₁ * x) + b * (y₁ * x) + c * z = 1 := by
    rw [hg1] at bz1; rw [bz2] at bz1; linear_combination -bz1
  set u := r * (x₁ * x) + (s - p) * (y₁ * x) - q * z with hu
  have hau : r = a * u := by
    linear_combination (-(y₁ * x)) * R21 + z * R11 - r * hbez
  have hbu : s - p = b * u := by
    linear_combination (x₁ * x) * R21 + z * R12 - (s - p) * hbez
  have hcu : q = -(c * u) := by
    linear_combination (x₁ * x) * R11 + (y₁ * x) * R12 - q * hbez
  refine ⟨u, hau, hcu, by linarith, ?_⟩
  simp only [disc, discrim]
  have hs : s = p + b * u := by linarith
  rw [hs, hau, hcu] at hdet
  linear_combination 4 * hdet

theorem automorph_trivial {F : ℤ × ℤ × ℤ} {p q r s : ℤ} (hcont : cont F = 1)
    (hD : disc F < -4) (hdet : p * s - q * r = 1) (hact : act F p q r s = F) :
    q = 0 ∧ r = 0 ∧ ((p = 1 ∧ s = 1) ∨ (p = -1 ∧ s = -1)) := by
  obtain ⟨u, hr, hq, hs, h4⟩ := automorph hcont hdet hact
  have hu : u = 0 := by
    by_contra hu
    have := one_le_sq_of_ne hu
    nlinarith [sq_nonneg (2 * p + F.2.1 * u)]
  subst hu
  simp only [mul_zero, neg_zero, add_zero] at hr hq hs h4
  refine ⟨hq, hr, ?_⟩
  have hp : (p - 1) * (p + 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hp with h | h
  · left; constructor <;> linarith
  · right; constructor <;> linarith

theorem crt_exists (f : ℤ) (x : f.natAbs.primeFactors → ℤ) :
    ∃ t : ℤ, ∀ i : f.natAbs.primeFactors, ((i : ℕ) : ℤ) ∣ t - x i := by
  have hpw : Pairwise (Function.onFun IsCoprime
      (fun i : f.natAbs.primeFactors => Ideal.span {((i : ℕ) : ℤ)})) := by
    intro i j hij
    simp only [Function.onFun]
    rw [Ideal.isCoprime_span_singleton_iff, Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
    have hi := (Nat.mem_primeFactors.mp i.2).1
    have hj := (Nat.mem_primeFactors.mp j.2).1
    exact (Nat.coprime_primes hi hj).mpr (fun h => hij (Subtype.ext h))
  obtain ⟨t, ht⟩ := Ideal.exists_forall_sub_mem_ideal hpw x
  exact ⟨t, fun i => Ideal.mem_span_singleton.mp (ht i)⟩

theorem dvd_val_sub_of_dvd {F : ℤ × ℤ × ℤ} {m x x' y : ℤ} (h : m ∣ x - x') :
    m ∣ val F x y - val F x' y := by
  obtain ⟨u, hu⟩ := h
  refine ⟨F.1 * (2 * x' * u + m * u ^ 2) + F.2.1 * u * y, ?_⟩
  have hx : x = x' + m * u := by linarith
  subst hx
  simp only [val]; ring

theorem dvd_val_sub_of_dvd' {F : ℤ × ℤ × ℤ} {m x y y' : ℤ} (h : m ∣ y - y') :
    m ∣ val F x y - val F x y' := by
  obtain ⟨u, hu⟩ := h
  refine ⟨F.2.1 * x * u + F.2.2 * (2 * y' * u + m * u ^ 2), ?_⟩
  have hy : y = y' + m * u := by linarith
  subst hy
  simp only [val]; ring

theorem roots_congr {F : ℤ × ℤ × ℤ} (hF : cont F = 1) {p : ℕ} (hp : p.Prime) {t : ℤ}
    (ht : (∃ x, (p : ℤ) ∣ val F x 1) → (p : ℤ) ∣ val F t 1) {j₁ j₂ : ℤ}
    (h₁ : (p : ℤ) ∣ val (act F 1 t 0 1) 1 j₁) (h₂ : (p : ℤ) ∣ val (act F 1 t 0 1) 1 j₂) :
    (p : ℤ) ∣ j₁ - j₂ := by
  have : Fact p.Prime := ⟨hp⟩
  set F' := act F 1 t 0 1 with hF'
  have hcF' : cont F' = 1 := by rw [hF', cont_act (by ring)]; exact hF
  have hvF' : ∀ x y, val F' x y = F'.1 * x ^ 2 + F'.2.1 * x * y + F'.2.2 * y ^ 2 :=
    fun _ _ => rfl
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at h₁ h₂ ⊢
  rw [hvF'] at h₁ h₂
  push_cast at h₁ h₂ ⊢
  by_cases hA : ∃ x, (p : ℤ) ∣ val F x 1
  · have hc : (p : ℤ) ∣ F'.2.2 := by
      have := ht hA
      have e : F'.2.2 = val F t 1 := by simp only [hF', act, val]
      rw [e]; exact this
    have hc' : ((F'.2.2 : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hc
    rw [hc'] at h₁ h₂
    by_cases hb : ((F'.2.1 : ℤ) : ZMod p) = 0
    · exfalso
      rw [hb] at h₁
      have ha : ((F'.1 : ℤ) : ZMod p) = 0 := by simpa using h₁
      have hpa := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp ha
      have hpb := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hb
      have h1 : (p : ℤ) ∣ ((1 : ℕ) : ℤ) := hcF' ▸ dvd_cont_iff.mpr ⟨hpa, hpb, hc⟩
      have : p ∣ 1 := Int.natCast_dvd_natCast.mp h1
      exact hp.one_lt.ne' (Nat.dvd_one.mp this)
    · have : ((F'.2.1 : ℤ) : ZMod p) * ((j₁ : ZMod p) - (j₂ : ZMod p)) = 0 := by
        linear_combination h₁ - h₂
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hb
      · exact h
  · push Not at hA
    have hnr : ∀ x : ℤ, ((F'.1 : ℤ) : ZMod p) * (x : ZMod p) ^ 2 +
        ((F'.2.1 : ℤ) : ZMod p) * (x : ZMod p) + ((F'.2.2 : ℤ) : ZMod p) ≠ 0 := by
      intro x hx
      have e : val F' x 1 = val F (x + t) 1 := by simp only [hF', act, val]; ring
      apply hA (x + t)
      rw [← e, ← ZMod.intCast_zmod_eq_zero_iff_dvd, hvF']
      push_cast
      linear_combination hx
    have hz : ∀ j : ℤ, ((F'.1 : ℤ) : ZMod p) * 1 + ((F'.2.1 : ℤ) : ZMod p) * 1 * (j : ZMod p) +
        ((F'.2.2 : ℤ) : ZMod p) * (j : ZMod p) ^ 2 = 0 → (j : ZMod p) = 0 := by
      intro j hj
      by_contra hne
      set w : ZMod p := (j : ZMod p)⁻¹ with hw
      have hwj : w * (j : ZMod p) = 1 := inv_mul_cancel₀ hne
      apply hnr ((w.val : ℕ) : ℤ)
      have hcast : (((w.val : ℕ) : ℤ) : ZMod p) = w := by simp
      rw [hcast]
      have hj2 : (j : ZMod p) ^ 2 ≠ 0 := pow_ne_zero 2 hne
      have : (j : ZMod p) ^ 2 * (((F'.1 : ℤ) : ZMod p) * w ^ 2 + ((F'.2.1 : ℤ) : ZMod p) * w +
          ((F'.2.2 : ℤ) : ZMod p)) = 0 := by
        linear_combination (((F'.1 : ℤ) : ZMod p) * (w * (j : ZMod p) + 1) +
          ((F'.2.1 : ℤ) : ZMod p) * (j : ZMod p)) * hwj + hj
      exact (mul_eq_zero.mp this).resolve_left hj2
    rw [hz j₁ h₁, hz j₂ h₂]; ring

theorem exists_good {F : ℤ × ℤ × ℤ} (hF : cont F = 1) {f : ℤ} (hf : f ≠ 0) :
    ∃ p q r s : ℤ, p * s - q * r = 1 ∧
      ∀ k, IsCoprime k f → IsCoprime (val (act F p q r s) 1 k) f := by
  classical
  let tp : f.natAbs.primeFactors → ℤ := fun i =>
    if h : ∃ x, ((i : ℕ) : ℤ) ∣ val F x 1 then h.choose else 0
  obtain ⟨t, ht⟩ := crt_exists f tp
  have htroot : ∀ i : f.natAbs.primeFactors, (∃ x, ((i : ℕ) : ℤ) ∣ val F x 1) →
      ((i : ℕ) : ℤ) ∣ val F t 1 := by
    intro i hex
    have h1 := ht i
    simp only [tp, hex, ↓reduceDIte] at h1
    have h2 := dvd_val_sub_of_dvd (F := F) (y := 1) h1
    have := dvd_add h2 hex.choose_spec
    simpa using this
  set F' := act F 1 t 0 1 with hF'
  let rp : f.natAbs.primeFactors → ℤ := fun i =>
    if h : ∃ j, ((i : ℕ) : ℤ) ∣ val F' 1 j then h.choose else 0
  obtain ⟨r, hr⟩ := crt_exists f rp
  refine ⟨1 + t * r, t, r, 1, by ring, ?_⟩
  intro k hk
  have e : val (act F (1 + t * r) t r 1) 1 k = val F' 1 (r + k) := by
    simp only [hF', val, act]; ring
  rw [e, Int.isCoprime_iff_gcd_eq_one]
  by_contra hne
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
  have hpd' : (p : ℤ) ∣ (Int.gcd (val F' 1 (r + k)) f : ℤ) := Int.natCast_dvd_natCast.mpr hpd
  have hp1 : (p : ℤ) ∣ val F' 1 (r + k) := hpd'.trans (Int.gcd_dvd_left _ _)
  have hp2 : (p : ℤ) ∣ f := hpd'.trans (Int.gcd_dvd_right _ _)
  have hpmem : p ∈ f.natAbs.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, Int.natCast_dvd.mp hp2, by simpa using hf⟩
  let i : f.natAbs.primeFactors := ⟨p, hpmem⟩
  have hex : ∃ j, ((i : ℕ) : ℤ) ∣ val F' 1 j := ⟨_, hp1⟩
  have hrp : (p : ℤ) ∣ val F' 1 (rp i) := by
    have := hex.choose_spec
    simp only [rp, hex, ↓reduceDIte]
    exact this
  have hrr : (p : ℤ) ∣ val F' 1 r := by
    have h1 := dvd_val_sub_of_dvd' (F := F') (x := 1) (hr i)
    have := dvd_add h1 hrp
    simpa using this
  have hk' : (p : ℤ) ∣ (r + k) - r := roots_congr hF hp (htroot i) hp1 hrr
  have hpk : (p : ℤ) ∣ k := by simpa using hk'
  have hu : IsUnit (p : ℤ) := hk.isUnit_of_dvd' hpk hp2
  rw [Int.isUnit_iff] at hu
  rcases hu with h | h
  · exact hp.one_lt.ne' (by exact_mod_cast h)
  · have : (0 : ℤ) ≤ p := by positivity
    omega

theorem val_pos {F : ℤ × ℤ × ℤ} (ha : 0 < F.1) (hd : disc F < 0) {x y : ℤ}
    (hxy : x ≠ 0 ∨ y ≠ 0) : 0 < val F x y := by
  obtain ⟨a, b, c⟩ := F
  simp only [disc, discrim, val] at *
  have key : 4 * a * (a * x ^ 2 + b * x * y + c * y ^ 2) =
      (2 * a * x + b * y) ^ 2 + (4 * a * c - b ^ 2) * y ^ 2 := by ring
  by_cases hy : y = 0
  · subst hy
    have hx : x ≠ 0 := hxy.resolve_right (not_not.mpr rfl)
    have := one_le_sq_of_ne hx
    nlinarith
  · have h1 := one_le_sq_of_ne hy
    have h2 : 0 < 4 * a * (a * x ^ 2 + b * x * y + c * y ^ 2) := by
      rw [key]; nlinarith [sq_nonneg (2 * a * x + b * y)]
    by_contra hneg
    push Not at hneg
    nlinarith

/-- Gauss reducedness is decidable, as in the definition of `reducedFormsOfDiscriminant`. -/
local instance decidableIsGaussReducedLocal (a b c : ℤ) : Decidable (IsGaussReduced a b c) :=
  inferInstanceAs (Decidable (0 < a ∧ discrim a b c < 0 ∧ |b| ≤ a ∧ a ≤ c ∧
    ((|b| = a ∨ a = c) → 0 ≤ b)))

theorem mem_reducedForms {d : ℤ} {q : ℤ × ℤ × ℤ} :
    q ∈ reducedFormsOfDiscriminant d ↔
      IsGaussReduced q.1 q.2.1 q.2.2 ∧ discrim q.1 q.2.1 q.2.2 = d := by
  unfold reducedFormsOfDiscriminant
  rw [Finset.mem_filter]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  obtain ⟨hred, hd⟩ := h
  obtain ⟨a, b, c⟩ := q
  simp only at hred hd ⊢
  have ha := hred.pos
  have hb := hred.abs_le
  have hac := hred.le
  have hbl := (abs_le.mp hb).1
  have hbu := (abs_le.mp hb).2
  have hb2 : b ^ 2 ≤ a ^ 2 := by nlinarith [sq_abs b, abs_nonneg b]
  have h3 : 3 * a ^ 2 ≤ -d := by rw [← hd]; unfold discrim; nlinarith
  rw [Finset.mem_biUnion]
  refine ⟨a, ?_, ?_⟩
  · rw [Finset.mem_Icc]
    refine ⟨ha, ?_⟩
    have hle : a.toNat * a.toNat ≤ (-d).toNat := by
      have : (a.toNat : ℤ) * a.toNat ≤ ((-d).toNat : ℤ) := by
        rw [Int.toNat_of_nonneg ha.le, Int.toNat_of_nonneg (by nlinarith)]; nlinarith
      exact_mod_cast this
    have := Nat.le_sqrt.mpr hle
    have e : ((a.toNat : ℕ) : ℤ) = a := Int.toNat_of_nonneg ha.le
    omega
  · rw [Finset.mem_image]
    refine ⟨b, Finset.mem_Icc.mpr ⟨hbl, hbu⟩, ?_⟩
    have : b ^ 2 - d = 4 * a * c := by rw [← hd]; unfold discrim; ring
    rw [this, Int.mul_ediv_cancel_left _ (by positivity)]

theorem gaussClassNumber_eq (d : ℤ) :
    gaussClassNumber d = ((reducedFormsOfDiscriminant d).filter fun q => cont q = 1).card := rfl

/-- A Gauss-reduced form properly equivalent to `G`, when `G` is positive definite. -/
noncomputable def red (G : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  if h : 0 < G.1 ∧ disc G < 0 then (exists_formEquiv_reduced G h.1 h.2).choose else G

theorem red_spec {G : ℤ × ℤ × ℤ} (h1 : 0 < G.1) (h2 : disc G < 0) :
    FormEquiv G (red G) ∧ IsGaussReduced (red G).1 (red G).2.1 (red G).2.2 := by
  have h : 0 < G.1 ∧ disc G < 0 := ⟨h1, h2⟩
  simp only [red, h, and_self, ↓reduceDIte]
  exact (exists_formEquiv_reduced G h1 h2).choose_spec

/-- A proper transformation of `F` after which every `k` prime to `f` gives
`gcd(F(1, k), f) = 1`. -/
noncomputable def goodMat (F : ℤ × ℤ × ℤ) (f : ℤ) : ℤ × ℤ × ℤ × ℤ :=
  if h : cont F = 1 ∧ f ≠ 0 then
    ((exists_good h.1 h.2).choose, (exists_good h.1 h.2).choose_spec.choose,
      (exists_good h.1 h.2).choose_spec.choose_spec.choose,
      (exists_good h.1 h.2).choose_spec.choose_spec.choose_spec.choose)
  else (1, 0, 0, 1)

/-- `F` moved by `goodMat F f`. -/
noncomputable def star (F : ℤ × ℤ × ℤ) (f : ℤ) : ℤ × ℤ × ℤ :=
  act F (goodMat F f).1 (goodMat F f).2.1 (goodMat F f).2.2.1 (goodMat F f).2.2.2

theorem star_spec {F : ℤ × ℤ × ℤ} (hF : cont F = 1) {f : ℤ} (hf : f ≠ 0) :
    FormEquiv F (star F f) ∧ ∀ k, IsCoprime k f → IsCoprime (val (star F f) 1 k) f := by
  have h : cont F = 1 ∧ f ≠ 0 := ⟨hF, hf⟩
  have hs := (exists_good h.1 h.2).choose_spec.choose_spec.choose_spec.choose_spec
  have hm : goodMat F f = ((exists_good h.1 h.2).choose, (exists_good h.1 h.2).choose_spec.choose,
      (exists_good h.1 h.2).choose_spec.choose_spec.choose,
      (exists_good h.1 h.2).choose_spec.choose_spec.choose_spec.choose) := by
    simp only [goodMat, h, ne_eq, not_false_eq_true, and_self, ↓reduceDIte]
  refine ⟨⟨_, _, _, _, ?_, rfl⟩, ?_⟩
  · rw [hm]; exact hs.1
  · intro k hk
    have := hs.2 k hk
    simp only [star]
    rw [hm]
    exact this

theorem main_gt4 {D : ℤ} (hD : D < -4) {f : ℕ} (hf : 0 < f) :
    gaussClassNumber D * f.totient ≤ gaussClassNumber ((f : ℤ) ^ 2 * D) := by
  classical
  have hcardK : ((Finset.range f).filter f.Coprime).card = f.totient :=
    (Nat.totient_eq_card_coprime f).symm
  rw [gaussClassNumber_eq, gaussClassNumber_eq, ← hcardK, ← Finset.card_product]
  have hfz : (f : ℤ) ≠ 0 := by exact_mod_cast hf.ne'
  -- facts about members
  have hS : ∀ F ∈ (reducedFormsOfDiscriminant D).filter (fun q => cont q = 1),
      IsGaussReduced F.1 F.2.1 F.2.2 ∧ disc F = D ∧ cont F = 1 := by
    intro F hF
    rw [Finset.mem_filter, mem_reducedForms] at hF
    exact ⟨hF.1.1, hF.1.2, hF.2⟩
  have hstar : ∀ F ∈ (reducedFormsOfDiscriminant D).filter (fun q => cont q = 1),
      FormEquiv F (star F f) ∧ (∀ k, IsCoprime k (f : ℤ) → IsCoprime (val (star F f) 1 k) f) ∧
      cont (star F f) = 1 ∧ disc (star F f) = D ∧ 0 < (star F f).1 := by
    intro F hF
    obtain ⟨hred, hd, hc⟩ := hS F hF
    obtain ⟨hE, hgood⟩ := star_spec hc hfz
    refine ⟨hE, hgood, by rw [hE.cont_eq, hc], by rw [hE.disc_eq, hd], ?_⟩
    obtain ⟨p, q, r, s, hdet, hact⟩ := hE
    have hpr : p ≠ 0 ∨ r ≠ 0 := by
      by_contra hcon; push Not at hcon; rw [hcon.1, hcon.2] at hdet; simp at hdet
    have := val_pos hred.pos (by rw [hd]; omega) hpr
    rw [← hact]; simpa [act, val] using this
  have hG : ∀ x ∈ ((reducedFormsOfDiscriminant D).filter (fun q => cont q = 1)) ×ˢ
      ((Finset.range f).filter f.Coprime),
      0 < (lift (star x.1 f) x.2 f).1 ∧ disc (lift (star x.1 f) x.2 f) < 0 ∧
      cont (lift (star x.1 f) x.2 f) = 1 ∧
      disc (lift (star x.1 f) x.2 f) = (f : ℤ) ^ 2 * D ∧
      IsCoprime (val (star x.1 f) 1 x.2) f := by
    intro x hx
    rw [Finset.mem_product] at hx
    obtain ⟨hE, hgood, hc, hd, hpos⟩ := hstar x.1 hx.1
    have hk : IsCoprime (x.2 : ℤ) (f : ℤ) :=
      Nat.isCoprime_iff_coprime.mpr (Finset.mem_filter.mp hx.2).2.symm
    have hcop := hgood _ hk
    have hdl : disc (lift (star x.1 f) x.2 f) = (f : ℤ) ^ 2 * D := by rw [disc_lift, hd]
    refine ⟨?_, ?_, cont_lift hc hcop, hdl, hcop⟩
    · rw [lift_eq]; exact val_pos hpos (by rw [hd]; omega) (Or.inl one_ne_zero)
    · rw [hdl]; have : (0 : ℤ) < (f : ℤ) ^ 2 := by positivity
      nlinarith
  apply Finset.card_le_card_of_injOn (fun x => red (lift (star x.1 f) x.2 f))
  · intro x hx
    obtain ⟨h1, h2, h3, h4, -⟩ := hG x hx
    obtain ⟨hE, hred⟩ := red_spec h1 h2
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨mem_reducedForms.mpr ⟨hred, ?_⟩, by rw [hE.cont_eq, h3]⟩
    have := hE.disc_eq
    simp only [disc] at this h4
    rw [this, h4]
  · intro x hx y hy hxy
    simp only at hxy
    obtain ⟨h1, h2, -, -, hcop⟩ := hG x hx
    obtain ⟨h1', h2', -, -, -⟩ := hG y hy
    have hEx := (red_spec h1 h2).1
    have hEy := (red_spec h1' h2').1
    rw [hxy] at hEx
    have hE : FormEquiv (lift (star x.1 f) x.2 f) (lift (star y.1 f) y.2 f) := hEx.trans hEy.symm
    obtain ⟨α, β, γ, δ, hdet, hact⟩ := hE
    obtain ⟨β₁, hβ, hN, hNdet⟩ := key hfz hdet hact hcop
    have hx' := Finset.mem_product.mp hx
    have hy' := Finset.mem_product.mp hy
    obtain ⟨hEx1, -, hcx, hdx, -⟩ := hstar x.1 hx'.1
    obtain ⟨hEy1, -, -, -, -⟩ := hstar y.1 hy'.1
    have hFF : FormEquiv x.1 y.1 :=
      hEx1.trans (FormEquiv.trans ⟨_, _, _, _, hNdet, hN⟩ hEy1.symm)
    have hF : x.1 = y.1 :=
      eq_of_formEquiv_of_reduced (hS x.1 hx'.1).1 (hS y.1 hy'.1).1 hFF
    rw [← hF] at hN
    obtain ⟨hq, hr, hps⟩ := automorph_trivial hcx (by rw [hdx]; exact hD) hNdet hN
    subst hq
    have hk : (f : ℤ) ∣ (x.2 : ℤ) - (y.2 : ℤ) := by
      rcases hps with ⟨hp, hs⟩ | ⟨hp, hs⟩
      · simp only [zero_mul, sub_zero, mul_zero, zero_add] at hp hs hr
        exact ⟨-γ, by rw [hp, hs] at hr; linear_combination hr⟩
      · simp only [zero_mul, sub_zero, mul_zero, zero_add] at hp hs hr
        exact ⟨γ, by rw [hp, hs] at hr; linear_combination -hr⟩
    have hxk := Finset.mem_range.mp (Finset.mem_filter.mp hx'.2).1
    have hyk := Finset.mem_range.mp (Finset.mem_filter.mp hy'.2).1
    obtain ⟨m, hm⟩ := hk
    have hm0 : m = 0 := by
      have h1 : ((x.2 : ℕ) : ℤ) < f := by exact_mod_cast hxk
      have h2 : ((y.2 : ℕ) : ℤ) < f := by exact_mod_cast hyk
      have h3 : (0 : ℤ) ≤ (x.2 : ℕ) := by positivity
      have h4 : (0 : ℤ) ≤ (y.2 : ℕ) := by positivity
      have hfpos : (0 : ℤ) < f := by exact_mod_cast hf
      rcases lt_trichotomy m 0 with hlt | heq | hgt
      · nlinarith
      · exact heq
      · nlinarith
    rw [hm0, mul_zero, sub_eq_zero] at hm
    exact Prod.ext hF (by exact_mod_cast hm)

/-- The automorph attached to an equivalence of `lift Fs k₀ f` with `lift Fs k f`, recorded by
its normalized parameters `uw` up to a sign `ε`. -/
def Pdata (Fs : ℤ × ℤ × ℤ) (f k₀ k : ℤ) (uw : ℤ × ℤ) : Prop :=
  ∃ α β γ δ β₁ ε : ℤ, ε * ε = 1 ∧ α * δ - β * γ = 1 ∧ β = f * β₁ ∧
    k₀ * α + f * γ - k₀ * β₁ * k - δ * k = Fs.1 * (ε * uw.1) ∧
    β₁ = -(Fs.2.2 * (ε * uw.1)) ∧
    k₀ * β₁ + δ = (α - β₁ * k) + Fs.2.1 * (ε * uw.1) ∧
    2 * (α - β₁ * k) + Fs.2.1 * (ε * uw.1) = ε * uw.2

theorem Pdata_inj {Fs : ℤ × ℤ × ℤ} {f k₀ k k' : ℤ} {uw : ℤ × ℤ} (hf : 0 < f)
    (hk : 0 ≤ k ∧ k < f) (hk' : 0 ≤ k' ∧ k' < f)
    (h : Pdata Fs f k₀ k uw) (h' : Pdata Fs f k₀ k' uw) : k = k' := by
  obtain ⟨α, β, γ, δ, β₁, ε, hε, hdet, hβ, H3, H2, H4, H1⟩ := h
  obtain ⟨α', β', γ', δ', β₁', ε', hε', hdet', hβ', H3', H2', H4', H1'⟩ := h'
  obtain ⟨u, w⟩ := uw
  simp only at *
  set a := Fs.1
  set b := Fs.2.1
  set c := Fs.2.2
  have hn3 : k₀ * α + f * γ - k₀ * β₁ * k - δ * k =
      ε * ε' * (k₀ * α' + f * γ' - k₀ * β₁' * k' - δ' * k') := by
    linear_combination H3 - ε * ε' * H3' - a * ε * u * hε'
  have hn2 : β₁ = ε * ε' * β₁' := by
    linear_combination H2 - ε * ε' * H2' + c * ε * u * hε'
  have hn1 : α - β₁ * k = ε * ε' * (α' - β₁' * k') := by
    have : 2 * ((α - β₁ * k) - ε * ε' * (α' - β₁' * k')) = 0 := by
      linear_combination H1 - ε * ε' * H1' - ε * (w - b * u) * hε'
    linarith
  have hn4 : k₀ * β₁ + δ = ε * ε' * (k₀ * β₁' + δ') := by
    linear_combination H4 - ε * ε' * H4' + hn1 - b * ε * u * hε'
  have hmain : δ * (k - k') = f * (γ - ε * ε' * γ') := by
    linear_combination (-1) * hn3 - k' * hn4 + k₀ * hn1 + k₀ * k' * hn2
  have hcop : IsCoprime δ f := ⟨α, -(β₁ * γ), by rw [hβ] at hdet; linear_combination hdet⟩
  have hdvd : f ∣ δ * (k - k') := ⟨_, hmain⟩
  have hfk : f ∣ k - k' := hcop.symm.dvd_of_dvd_mul_left hdvd
  obtain ⟨m, hm⟩ := hfk
  have : m = 0 := by
    rcases lt_trichotomy m 0 with hlt | heq | hgt
    · nlinarith
    · exact heq
    · nlinarith
  rw [this, mul_zero, sub_eq_zero] at hm
  exact hm

/-- The normalized automorph parameters for the discriminants `-3` and `-4`. -/
def autSet (D : ℤ) : Finset (ℤ × ℤ) :=
  if D = -3 then {(0, 2), (1, 1), (1, -1)} else {(0, 2), (1, 0)}

theorem autSet_card (D : ℤ) : (autSet D).card ≤ 3 := by
  unfold autSet; split_ifs <;> decide

theorem mem_autSet {D u w : ℤ} (hD : D = -3 ∨ D = -4) (hu : 0 ≤ u) (hw : u = 0 → 0 < w)
    (h : w ^ 2 - D * u ^ 2 = 4) : (u, w) ∈ autSet D := by
  have hu1 : u ≤ 1 := by
    rcases hD with rfl | rfl <;> nlinarith [sq_nonneg w]
  have hw2 : w ≤ 2 := by rcases hD with rfl | rfl <;> nlinarith [sq_nonneg u]
  have hw2' : -2 ≤ w := by rcases hD with rfl | rfl <;> nlinarith [sq_nonneg u]
  rcases hD with rfl | rfl
  · interval_cases u <;> interval_cases w <;> simp_all [autSet]
  · interval_cases u <;> interval_cases w <;> simp_all [autSet]

theorem Pdata_exists {Fs : ℤ × ℤ × ℤ} (hc : cont Fs = 1) (hD : disc Fs = -3 ∨ disc Fs = -4)
    {f k₀ k : ℤ} (hf : f ≠ 0) (hcop : IsCoprime (val Fs 1 k₀) f)
    (hE : FormEquiv (lift Fs k₀ f) (lift Fs k f)) :
    ∃ uw ∈ autSet (disc Fs), Pdata Fs f k₀ k uw := by
  obtain ⟨α, β, γ, δ, hdet, hact⟩ := hE
  obtain ⟨β₁, hβ, hN, hNdet⟩ := key hf hdet hact hcop
  obtain ⟨u₀, h3, h2, h4, h1⟩ := automorph hc hNdet hN
  set w₀ := 2 * (α - β₁ * k) + Fs.2.1 * u₀ with hw₀
  by_cases hpos : 0 < u₀ ∨ (u₀ = 0 ∧ 0 < w₀)
  · refine ⟨(u₀, w₀), mem_autSet hD ?_ ?_ h1, α, β, γ, δ, β₁, 1, by ring, hdet, hβ, ?_, ?_, ?_, ?_⟩
    · rcases hpos with h | h <;> [exact h.le; exact h.1.ge]
    · intro hu; rcases hpos with h | h
      · omega
      · exact h.2
    · simp only; rw [h3]; ring
    · simp only; rw [h2]; ring
    · simp only; rw [h4]; ring
    · simp only; ring
  · push Not at hpos
    have hw0 : w₀ ≠ 0 ∨ u₀ ≠ 0 := by
      by_contra hcon; push Not at hcon
      rw [hcon.1, hcon.2] at h1; norm_num at h1
    refine ⟨(-u₀, -w₀), mem_autSet hD ?_ ?_ (by linear_combination h1),
      α, β, γ, δ, β₁, -1, by ring, hdet, hβ, ?_, ?_, ?_, ?_⟩
    · linarith [hpos.1]
    · intro hu
      have hu0 : u₀ = 0 := by linarith
      have := hpos.2 hu0
      rcases hw0 with h | h
      · omega
      · exact absurd hu0 h
    · simp only; rw [h3]; ring
    · simp only; rw [h2]; ring
    · simp only; rw [h4]; ring
    · simp only; ring

open Classical in
theorem fiber_le_three {Fs : ℤ × ℤ × ℤ} (hc : cont Fs = 1) (hD : disc Fs = -3 ∨ disc Fs = -4)
    {f : ℕ} (hf : 0 < f) {k₀ : ℕ} (hcop : IsCoprime (val Fs 1 k₀) f) (K : Finset ℕ)
    (hK : ∀ k ∈ K, k < f) :
    (K.filter fun k : ℕ =>
      FormEquiv (lift Fs (k₀ : ℤ) (f : ℤ)) (lift Fs (k : ℤ) (f : ℤ))).card ≤ 3 := by
  classical
  have hfz : (f : ℤ) ≠ 0 := by exact_mod_cast hf.ne'
  let σ : ℕ → ℤ × ℤ := fun k =>
    if h : ∃ uw ∈ autSet (disc Fs), Pdata Fs f k₀ k uw then h.choose else (0, 0)
  have hσ : ∀ k ∈ K.filter (fun k : ℕ =>
      FormEquiv (lift Fs (k₀ : ℤ) (f : ℤ)) (lift Fs (k : ℤ) (f : ℤ))),
      σ k ∈ autSet (disc Fs) ∧ Pdata Fs f k₀ k (σ k) := by
    intro k hk
    have hex := Pdata_exists hc hD hfz hcop (Finset.mem_filter.mp hk).2
    simp only [σ, hex, ↓reduceDIte]
    exact hex.choose_spec
  calc (K.filter fun k : ℕ => FormEquiv (lift Fs (k₀ : ℤ) (f : ℤ)) (lift Fs (k : ℤ) (f : ℤ))).card
      ≤ (autSet (disc Fs)).card := by
        apply Finset.card_le_card_of_injOn σ
        · intro k hk; exact (hσ k hk).1
        · intro k hk k' hk' hkk
          have h1 := (hσ k hk).2
          have h2 := (hσ k' hk').2
          rw [hkk] at h1
          have hkf := hK k (Finset.mem_filter.mp hk).1
          have hkf' := hK k' (Finset.mem_filter.mp hk').1
          have := Pdata_inj (by exact_mod_cast hf) ⟨by positivity, by exact_mod_cast hkf⟩
            ⟨by positivity, by exact_mod_cast hkf'⟩ h1 h2
          exact_mod_cast this
    _ ≤ 3 := autSet_card _

theorem main_small {D : ℤ} (hD : D = -3 ∨ D = -4) {f : ℕ} (hf : 0 < f) :
    f.totient ≤ 3 * gaussClassNumber ((f : ℤ) ^ 2 * D) := by
  classical
  have hfz : (f : ℤ) ≠ 0 := by exact_mod_cast hf.ne'
  -- a primitive positive definite form of discriminant `D`
  obtain ⟨F₀, hF₀a, hF₀d, hF₀c⟩ : ∃ F₀ : ℤ × ℤ × ℤ, 0 < F₀.1 ∧ disc F₀ = D ∧ cont F₀ = 1 := by
    rcases hD with rfl | rfl
    · exact ⟨(1, 1, 1), by norm_num, by norm_num [disc, discrim], by decide⟩
    · exact ⟨(1, 0, 1), by norm_num, by norm_num [disc, discrim], by decide⟩
  obtain ⟨hE, hgood⟩ := star_spec hF₀c hfz
  set Fs := star F₀ f
  have hc : cont Fs = 1 := by rw [hE.cont_eq, hF₀c]
  have hd : disc Fs = D := by rw [hE.disc_eq, hF₀d]
  have hDneg : D < 0 := by rcases hD with rfl | rfl <;> norm_num
  have hpos : 0 < Fs.1 := by
    obtain ⟨p, q, r, s, hdet, hact⟩ := hE
    have hpr : p ≠ 0 ∨ r ≠ 0 := by
      by_contra hcon; push Not at hcon; rw [hcon.1, hcon.2] at hdet; simp at hdet
    have := val_pos hF₀a (by rw [hF₀d]; exact hDneg) hpr
    rw [show Fs = act F₀ p q r s from hact.symm]; simpa [act, val] using this
  set K := (Finset.range f).filter f.Coprime
  have hcardK : K.card = f.totient := (Nat.totient_eq_card_coprime f).symm
  have hKcop : ∀ k ∈ K, IsCoprime (val Fs 1 (k : ℤ)) (f : ℤ) := by
    intro k hk
    exact hgood _ (Nat.isCoprime_iff_coprime.mpr (Finset.mem_filter.mp hk).2.symm)
  have hGfacts : ∀ k ∈ K, 0 < (lift Fs k f).1 ∧ disc (lift Fs k f) < 0 ∧
      cont (lift Fs k f) = 1 ∧ disc (lift Fs k f) = (f : ℤ) ^ 2 * D := by
    intro k hk
    have hdl : disc (lift Fs k f) = (f : ℤ) ^ 2 * D := by rw [disc_lift, hd]
    refine ⟨?_, ?_, cont_lift hc (hKcop k hk), hdl⟩
    · rw [lift_eq]; exact val_pos hpos (by rw [hd]; exact hDneg) (Or.inl one_ne_zero)
    · rw [hdl]; have : (0 : ℤ) < (f : ℤ) ^ 2 := by positivity
      nlinarith
  let Φ : ℕ → ℤ × ℤ × ℤ := fun k => red (lift Fs k f)
  have himg : K.image Φ ⊆
      (reducedFormsOfDiscriminant ((f : ℤ) ^ 2 * D)).filter (fun q => cont q = 1) := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨h1, h2, h3, h4⟩ := hGfacts k hk
    obtain ⟨hE', hred⟩ := red_spec h1 h2
    rw [Finset.mem_filter]
    refine ⟨mem_reducedForms.mpr ⟨hred, ?_⟩, by rw [hE'.cont_eq, h3]⟩
    have := hE'.disc_eq
    simp only [disc] at this h4
    rw [this, h4]
  have hfib : ∀ b ∈ K.image Φ, (K.filter fun k => Φ k = b).card ≤ 3 := by
    intro b hb
    obtain ⟨k₀, hk₀, rfl⟩ := Finset.mem_image.mp hb
    have hsub : (K.filter fun k => Φ k = Φ k₀) ⊆
        (K.filter fun k : ℕ => FormEquiv (lift Fs (k₀ : ℤ) (f : ℤ)) (lift Fs (k : ℤ) (f : ℤ))) := by
      intro k hk
      rw [Finset.mem_filter] at hk ⊢
      refine ⟨hk.1, ?_⟩
      obtain ⟨h1, h2, -, -⟩ := hGfacts k hk.1
      obtain ⟨h1', h2', -, -⟩ := hGfacts k₀ hk₀
      have e1 := (red_spec h1 h2).1
      have e2 := (red_spec h1' h2').1
      have hk2 : Φ k = Φ k₀ := hk.2
      simp only [Φ] at hk2
      rw [hk2] at e1
      exact e2.trans e1.symm
    refine (Finset.card_le_card hsub).trans ?_
    convert fiber_le_three hc (by rw [hd]; exact hD) hf (hKcop k₀ hk₀) K
      (fun k hk => Finset.mem_range.mp (Finset.mem_filter.mp hk).1)
  have := Finset.card_le_mul_card_image K 3 hfib
  rw [gaussClassNumber_eq]
  calc f.totient = K.card := hcardK.symm
    _ ≤ 3 * (K.image Φ).card := this
    _ ≤ 3 * _ := Nat.mul_le_mul_left 3 (Finset.card_le_card himg)

end GaussClassNumberTotient

open GaussClassNumberTotient in
/-- **Totient lower bounds for class numbers of imaginary quadratic orders.** Let $D < 0$ be a
fundamental discriminant, let $f \ge 1$ be an integer and let $\varphi$ be Euler's totient
function. If $D \notin \{-3, -4\}$, then the Gauss class numbers satisfy
$h(D)\, \varphi(f) \le h(f^2 D)$. If $D \in \{-3, -4\}$, then $\varphi(f) \le 3\, h(f^2 D)$.

Here $h(d)$ is the Gauss class number `gaussClassNumber d`, the number of primitive positive
definite Gauss-reduced binary quadratic forms of discriminant $d$.

Source: Guy Fowler, *Some uniform effective results on André–Oort for sums of powers in*
$\mathbb{C}^n$, Math. Proc. Cambridge Philos. Soc. 180 (2026), 607–641, proof of
Proposition 2·7, pp. 615–616, which derives both bounds from the class number formula for
imaginary quadratic orders (Cox, *Primes of the form* $x^2 + ny^2$, Theorem 7.24, as cited
there). -/
public theorem gaussClassNumber_mul_totient_le {D : ℤ}
    (hD : ImaginaryQuadraticDiscriminant.IsFundamentalImaginaryQuadraticDiscriminant D)
    {f : ℕ} (hf : 1 ≤ f) :
    (D ≠ -3 → D ≠ -4 → gaussClassNumber D * f.totient ≤ gaussClassNumber ((f : ℤ) ^ 2 * D)) ∧
      (D = -3 ∨ D = -4 → f.totient ≤ 3 * gaussClassNumber ((f : ℤ) ^ 2 * D)) := by
  have hdisc :=
    ImaginaryQuadraticDiscriminant.isFundamentalImaginaryQuadraticDiscriminant_isImaginary hD
  obtain ⟨hneg, hmod⟩ := hdisc
  refine ⟨fun h3 h4 => main_gt4 (by omega) hf, fun h => main_small h hf⟩

end MetaMathlibExt
