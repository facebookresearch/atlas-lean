/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.QuadraticForms.AlignedForms
public import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The form class group

For integer triples $(a, b, c)$, standing for the binary quadratic forms $ax^2 + bxy + cy^2$, this
file completes Knapp's construction of the form class group (*Advanced Algebra*, Chapter I, §4):

* `BinaryQuadraticForm.composition_class_well_defined` (Knapp's Theorem 1.12(b)): for aligned
  forms (primitive forms of one nonsquare discriminant with equal middle coefficients and an
  integral multiplier $j$), the proper equivalence class of their composition depends only on the
  classes of the forms;
* `BinaryQuadraticForm.FormClass D`: the proper equivalence classes of primitive forms of
  discriminant $D$, with `FormClass.mk_mul_mk`: for $D$ not a square, the product of two classes is
  the class of the composition of any aligned representatives;
* `FormClass.mul_identity`, `FormClass.mk_mul_mk_neg`, `FormClass.mul_assoc` (Knapp's
  Theorem 1.12(c)): the identity class, inverses and associativity;
* `FormClass.instCommGroup`: for $D$ not a square with $D \equiv 0$ or $1 \pmod 4$, the classes form
  an abelian group;
* `FormClass.posDefSubgroup`: for $D < 0$, the classes of positive definite forms form a subgroup
  (Knapp's remark after Theorem 1.12).

The source is Anthony W. Knapp, *Advanced Algebra*, digital second edition, published by the
author, East Setauket, NY, 2016, Chapter I, §4, pp. 25–31.
-/

@[expose] public section

namespace BinaryQuadraticForm

/-- **The last coefficient of a form is determined by the others and the discriminant.** If
$a \ne 0$ and $b^2 - 4ac = b^2 - 4ac'$, then $c = c'$.

Source: Anthony W. Knapp, *Advanced Algebra*, digital second edition, 2016, Chapter I, §4, p. 26:
in a form $(a, b', c')$ of discriminant $D$, $c' = (b'^2 - D)/(4a)$. -/
private theorem eq_of_discrim_eq {a b c c' : ℤ} (ha : a ≠ 0) (h : discrim a b c = discrim a b c') :
    c = c' := by
  simp only [discrim] at h
  exact mul_left_cancel₀ (mul_ne_zero four_ne_zero ha) (by linear_combination -h)

/-- **Middle coefficients of forms of one discriminant have the same parity.** If
$b'^2 - 4a'c' = b^2 - 4ac$, then $2 \mid b' - b$.

Source: Anthony W. Knapp, *Advanced Algebra*, digital second edition, 2016, Chapter I, §4, p. 28,
the proof of Theorem 1.12(a) ("$b_1 \equiv D \equiv b_2 \bmod 2$"). -/
private theorem two_dvd_sub_of_discrim_eq {a b c a' b' c' : ℤ}
    (h : discrim a' b' c' = discrim a b c) :
    2 ∣ b' - b := by
  obtain ⟨u, hu⟩ := Int.even_mul_pred_self b
  obtain ⟨u', hu'⟩ := Int.even_mul_pred_self b'
  simp only [discrim] at h
  exact ⟨2 * (a' * c' - a * c) - u' + u, by linear_combination -hu' + hu + h⟩

/-- **A common middle coefficient for two coprime first coefficients.** If $a_1$ and $a_2$ are
coprime and $b_2 - b_1$ is even, then some integer $B$ satisfies $B \equiv b_1 \pmod{2a_1}$ and
$B \equiv b_2 \pmod{2a_2}$.

Source: Anthony W. Knapp, *Advanced Algebra*, digital second edition, 2016, Chapter I, §4, p. 28,
the proof of Theorem 1.12(a) (the choice of $l_1$ and $l_2$ with
$2a_1 l_1 - 2a_2 l_2 = b_2 - b_1$). -/
private theorem exists_modEq_two_mul {a₁ a₂ b₁ b₂ : ℤ} (h : IsCoprime a₁ a₂) (hb : 2 ∣ b₂ - b₁) :
    ∃ B : ℤ, B ≡ b₁ [ZMOD 2 * a₁] ∧ B ≡ b₂ [ZMOD 2 * a₂] := by
  obtain ⟨u, v, huv⟩ := h
  obtain ⟨t, ht⟩ := hb
  exact ⟨b₁ + 2 * a₁ * (u * t), Int.modEq_iff_dvd.mpr ⟨-(u * t), by ring⟩,
    Int.modEq_iff_dvd.mpr ⟨v * t, by linear_combination ht - 2 * t * huv⟩⟩

/-- **A form with the same first coefficient, a congruent middle coefficient and the same
discriminant is properly equivalent.** If $a \ne 0$, $B = b + 2al$ and $(a, B, C)$ has the
discriminant of $(a, b, c)$, then $(a, B, C)$ is the translate of $(a, b, c)$ by $l$, and the two
forms are properly equivalent.

Source: Anthony W. Knapp, *Advanced Algebra*, digital second edition, 2016, Chapter I, §4, p. 26,
the paragraph before Lemma 1.10 (translates). -/
private theorem properlyEquivalent_of_eq_add {a b c B C l : ℤ} (ha : a ≠ 0) (hB : B = b + 2 * a * l)
    (hd : discrim a B C = discrim a b c) : ProperlyEquivalent (a, b, c) (a, B, C) := by
  have hC : C = a * l ^ 2 + b * l + c := by
    apply eq_of_discrim_eq ha (b := B)
    rw [hd, hB]
    simp only [discrim]
    ring
  subst hC hB
  exact properlyEquivalent_translate a b c l

/-- **The substitution $(x, y) \mapsto (-y, x)$.** The form $(a, b, c)$ is properly equivalent to
$(c, -b, a)$.

Source: Anthony W. Knapp, *Advanced Algebra*, digital second edition, 2016, Chapter I, §3,
the proof of Theorem 1.6(a), pp. 16–17 (the matrix $\begin{pmatrix} 0 & -1 \\ 1 & 0
\end{pmatrix}$ carries $(a, b, c)$ to $(c, -b, a)$). -/
theorem properlyEquivalent_swap (a b c : ℤ) : ProperlyEquivalent (a, b, c) (c, -b, a) :=
  properlyEquivalent_iff_exists.mpr ⟨0, -1, 1, 0, by ring, by
    simp only [Prod.mk.injEq]
    exact ⟨by ring, by ring, by ring⟩⟩

/-- **Changing the sign of the middle coefficients keeps proper equivalence.** If $(a, b, c)$ and
$(a', b', c')$ are properly equivalent, so are $(a, -b, c)$ and $(a', -b', c')$: conjugate the
substitution by $(x, y) \mapsto (x, -y)$.

Source: Anthony W. Knapp, *Advanced Algebra*, digital second edition, 2016, Chapter I, §4, Theorem
1.12(c), p. 28, where the inverse of the class of $(a, b, c)$ is the
class of $(a, -b, c)$, which uses this fact. -/
theorem ProperlyEquivalent.neg_middle {f g : ℤ × ℤ × ℤ} (h : ProperlyEquivalent f g) :
    ProperlyEquivalent (f.1, -f.2.1, f.2.2) (g.1, -g.2.1, g.2.2) := by
  obtain ⟨p, q, r, s, hdet, rfl⟩ := properlyEquivalent_iff_exists.mp h
  refine properlyEquivalent_iff_exists.mpr ⟨p, -q, -r, s, by linear_combination hdet, ?_⟩
  simp only [Prod.mk.injEq]
  exact ⟨by ring, by ring, by ring⟩

/-- Lemma 1.11 with the common factor written as a product, for a nonzero factor. -/
private theorem ProperlyEquivalent.mul_fst {a₁ a₂ b c₁ c₂ l : ℤ} (hl0 : l ≠ 0)
    (h : ProperlyEquivalent (a₁, b, l * c₁) (a₂, b, l * c₂))
    (hl : Int.gcd (Int.gcd a₁ a₂ : ℤ) l = 1) :
    ProperlyEquivalent (l * a₁, b, c₁) (l * a₂, b, c₂) := by
  have := h.mul_fst_div_snd hl (dvd_mul_right l c₁) (dvd_mul_right l c₂)
  rwa [Int.mul_ediv_cancel_left c₁ hl0, Int.mul_ediv_cancel_left c₂ hl0] at this

/-- **The step $(\ast\ast)$ of Knapp's proof of Theorem 1.12(b).** Let $(a_1, b, c_1)$ and
$(a_2, b, c_2)$ be forms with $c_1 = j a_2$ and $c_2 = j a_1$, and let $(a_1', b', c_1')$ and
$(a_2', b', c_2')$ be forms with $c_1' = j' a_2'$ and $c_2' = j' a_1'$. Suppose that $(a_1, b, c_1)$
is properly equivalent to $(a_1', b', c_1')$, that $(a_2, b, c_2)$ is properly equivalent to
$(a_2', b', c_2')$, that the discriminant $b^2 - 4a_1c_1$ is not the square of an integer, and that
$a_1 a_2$ is prime to $a_1' a_2'$. Then $(a_1 a_2, b, j)$ and $(a_1' a_2', b', j')$ are properly
equivalent.

In Knapp's proof the two pairs are aligned, so the four forms are primitive, and
$\gcd(a_1, a_2) = 1$. The proof uses neither hypothesis, and both are left out here.

Source: Anthony W. Knapp, *Advanced Algebra*, digital second edition, 2016, Chapter I, §4, the
proof of Theorem 1.12(b), pp. 29–30 (from "We can now argue as in the proof of Theorem 1.12a" to
the end of the proof), with footnote 7, p. 26. -/
theorem ProperlyEquivalent.composition_of_coprime {a₁ a₂ b c₁ c₂ j a₁' a₂' b' c₁' c₂' j' : ℤ}
    (hD : ¬ IsSquare (discrim a₁ b c₁))
    (hj₁ : c₁ = j * a₂) (hj₂ : c₂ = j * a₁) (hj₁' : c₁' = j' * a₂') (hj₂' : c₂' = j' * a₁')
    (h₁ : ProperlyEquivalent (a₁, b, c₁) (a₁', b', c₁'))
    (h₂ : ProperlyEquivalent (a₂, b, c₂) (a₂', b', c₂'))
    (hcop : IsCoprime (a₁ * a₂) (a₁' * a₂')) :
    ProperlyEquivalent (a₁ * a₂, b, j) (a₁' * a₂', b', j') := by
  have hdisc' : discrim a₁' b' c₁' = discrim a₁ b c₁ := h₁.discrim_eq
  have hdisc : b' ^ 2 - 4 * a₁' * c₁' = b ^ 2 - 4 * a₁ * c₁ := hdisc'
  have hsq : ∀ {a c : ℤ} (b₀ : ℤ), b₀ ^ 2 - 4 * a * c = b ^ 2 - 4 * a₁ * c₁ → a ≠ 0 := by
    intro a c b₀ h
    exact fst_ne_zero_of_not_isSquare (b := b₀) (c := c)
      (by change ¬ IsSquare (b₀ ^ 2 - 4 * a * c); rw [h]; exact hD)
  have ha₁ : a₁ ≠ 0 := hsq b rfl
  have ha₂ : a₂ ≠ 0 := hsq (c := c₂) b (by rw [hj₁, hj₂]; ring)
  have ha₁' : a₁' ≠ 0 := hsq b' hdisc
  have ha₂' : a₂' ≠ 0 := hsq (c := c₂') b' (by rw [← hdisc, hj₁', hj₂']; ring)
  have hc₁ : IsCoprime a₁ (a₁' * a₂') := hcop.of_mul_left_left
  have hc₂ : IsCoprime a₁ a₂' := hc₁.of_mul_right_right
  obtain ⟨B, hB, hB'⟩ := exists_modEq_two_mul hcop (two_dvd_sub_of_discrim_eq hdisc')
  obtain ⟨l, hl⟩ : 2 * (a₁ * a₂) ∣ B - b := hB.symm.dvd
  obtain ⟨l', hl'⟩ : 2 * (a₁' * a₂') ∣ B - b' := hB'.symm.dvd
  obtain ⟨n, hn⟩ : ∃ n, B ^ 2 - (b ^ 2 - 4 * a₁ * c₁) = 4 * (a₁ * a₂) * n :=
    ⟨a₁ * a₂ * l ^ 2 + b * l + j, by
      rw [hj₁]; linear_combination (B + b + 2 * (a₁ * a₂) * l) * hl⟩
  obtain ⟨k, hk⟩ : ∃ k, B ^ 2 - (b ^ 2 - 4 * a₁ * c₁) = 4 * (a₁' * a₂') * k :=
    ⟨a₁' * a₂' * l' ^ 2 + b' * l' + j', by
      rw [← hdisc, hj₁']; linear_combination (B + b' + 2 * (a₁' * a₂') * l') * hl'⟩
  obtain ⟨m, hm⟩ : a₁ ∣ k := hc₁.dvd_of_dvd_mul_left ⟨a₂ * n,
    mul_left_cancel₀ (four_ne_zero (α := ℤ)) (by linear_combination hn - hk)⟩
  have hX : B ^ 2 - (b ^ 2 - 4 * a₁ * c₁) = 4 * (a₁' * a₂') * (a₁ * m) := by rw [hk, hm]
  have E₁ : ProperlyEquivalent (a₁, b, c₁) (a₁, B, a₂' * (a₁' * m)) :=
    properlyEquivalent_of_eq_add ha₁ (l := a₂ * l) (by linear_combination hl)
      (by simp only [discrim]; linear_combination hX)
  have E₂ : ProperlyEquivalent (a₁', b', c₁') (a₁', B, a₂' * (a₁ * m)) :=
    properlyEquivalent_of_eq_add ha₁' (l := a₂' * l') (by linear_combination hl')
      (by simp only [discrim]; linear_combination hX - hdisc)
  have E₃ : ProperlyEquivalent (a₂, b, c₂) (a₂, B, a₁ * n) :=
    properlyEquivalent_of_eq_add ha₂ (l := a₁ * l) (by linear_combination hl)
      (by simp only [discrim]; linear_combination hn + 4 * a₂ * hj₂ - 4 * a₁ * hj₁)
  have E₄ : ProperlyEquivalent (a₂', b', c₂') (a₂', B, a₁ * (a₁' * m)) :=
    properlyEquivalent_of_eq_add ha₂' (l := a₁' * l') (by linear_combination hl')
      (by simp only [discrim]
          linear_combination hX - hdisc + 4 * a₂' * hj₂' - 4 * a₁' * hj₁')
  have E₅ : ProperlyEquivalent (a₁ * a₂, b, j) (a₁ * a₂, B, n) :=
    properlyEquivalent_of_eq_add (mul_ne_zero ha₁ ha₂) (l := l) (by linear_combination hl)
      (by simp only [discrim]; linear_combination hn - 4 * a₁ * hj₁)
  have E₆ : ProperlyEquivalent (a₁' * a₂', b', j') (a₁' * a₂', B, a₁ * m) :=
    properlyEquivalent_of_eq_add (mul_ne_zero ha₁' ha₂') (l := l') (by linear_combination hl')
      (by simp only [discrim]; linear_combination hX - hdisc - 4 * a₁' * hj₁')
  have hA := ProperlyEquivalent.mul_fst ha₂' (E₁.symm.trans (h₁.trans E₂))
    (Int.isCoprime_iff_gcd_eq_one.mp (hc₂.of_isCoprime_of_dvd_left (Int.gcd_dvd_left _ _)))
  have hB₂ := ProperlyEquivalent.mul_fst ha₁ (E₃.symm.trans (h₂.trans E₄))
    (Int.isCoprime_iff_gcd_eq_one.mp (hc₂.symm.of_isCoprime_of_dvd_left (Int.gcd_dvd_right _ _)))
  rw [mul_comm a₂' a₁, mul_comm a₂' a₁'] at hA
  exact E₅.trans (hB₂.trans (hA.trans E₆.symm))

/-- **The class of a composition of aligned forms depends only on their classes (Knapp's
Theorem 1.12(b)).** Let $(a_1', b', c_1')$ and $(a_2', b', c_2')$ be primitive forms with
$c_1' = j' a_2'$ and $c_2' = j' a_1'$, whose discriminant $D = b'^2 - 4a_1'c_1'$ is not the square
of an integer; they are aligned in Knapp's sense. Let $(a_1'', b'', c_1'')$ and
$(a_2'', b'', c_2'')$ be forms with $c_1'' = j'' a_2''$ and $c_2'' = j'' a_1''$, with
$(a_1'', b'', c_1'')$ properly equivalent to $(a_1', b', c_1')$ and $(a_2'', b'', c_2'')$ properly
equivalent to $(a_2', b', c_2')$; they are then primitive of discriminant $D$
(`properlyEquivalent_invariants`), so aligned too. Then the compositions $(a_1' a_2', b', j')$ and
$(a_1'' a_2'', b'', j'')$ are properly equivalent. Both compositions are primitive of
discriminant $D$ (`composition_of_aligned`).

Source: Anthony W. Knapp, *Advanced Algebra*, digital second edition, 2016, Chapter I, §4,
Theorem 1.12(b), p. 28, with its proof, pp. 28–30. -/
theorem composition_class_well_defined
    {a₁' a₂' b' c₁' c₂' j' a₁'' a₂'' b'' c₁'' c₂'' j'' : ℤ}
    (hp₁ : Int.gcd (Int.gcd a₁' b' : ℤ) c₁' = 1) (hp₂ : Int.gcd (Int.gcd a₂' b' : ℤ) c₂' = 1)
    (hD : ¬ IsSquare (discrim a₁' b' c₁'))
    (hj₁' : c₁' = j' * a₂') (hj₂' : c₂' = j' * a₁')
    (hj₁'' : c₁'' = j'' * a₂'') (hj₂'' : c₂'' = j'' * a₁'')
    (h₁ : ProperlyEquivalent (a₁', b', c₁') (a₁'', b'', c₁''))
    (h₂ : ProperlyEquivalent (a₂', b', c₂') (a₂'', b'', c₂'')) :
    ProperlyEquivalent (a₁' * a₂', b', j') (a₁'' * a₂'', b'', j'') := by
  have hdisc₂ : discrim a₂' b' c₂' = discrim a₁' b' c₁' := by
    simp only [discrim]; rw [hj₁', hj₂']; ring
  have hne : ∀ {a b₀ c : ℤ}, discrim a b₀ c = discrim a₁' b' c₁' → a ≠ 0 :=
    fun h => fst_ne_zero_of_not_isSquare (by rw [h]; exact hD)
  have hm : a₁' * a₂' * (a₁'' * a₂'') ≠ 0 :=
    mul_ne_zero (mul_ne_zero (hne rfl) (hne hdisc₂))
      (mul_ne_zero (hne h₁.discrim_eq) (hne (h₂.discrim_eq.trans hdisc₂)))
  obtain ⟨a₁, a₂, b, c₁, c₂, j, e₁, e₂, hj₁, hj₂, -, hm₁, hm₂⟩ :=
    exists_aligned (f₁ := (a₁', b', c₁')) (f₂ := (a₂', b', c₂')) hp₁ hp₂ hD hdisc₂ hm
  have hcm : IsCoprime (a₁ * a₂) (a₁' * a₂' * (a₁'' * a₂'')) :=
    (Int.isCoprime_iff_gcd_eq_one.mpr hm₁).mul_left (Int.isCoprime_iff_gcd_eq_one.mpr hm₂)
  have hD₀ : ¬ IsSquare (discrim a₁ b c₁) := by
    rw [(e₁.discrim_eq : discrim a₁ b c₁ = discrim a₁' b' c₁')]; exact hD
  have k₁ := ProperlyEquivalent.composition_of_coprime hD₀ hj₁ hj₂ hj₁' hj₂' e₁.symm e₂.symm
    (hcm.of_isCoprime_of_dvd_right (dvd_mul_right _ _))
  have k₂ := ProperlyEquivalent.composition_of_coprime hD₀ hj₁ hj₂ hj₁'' hj₂''
    (e₁.symm.trans h₁) (e₂.symm.trans h₂) (hcm.of_isCoprime_of_dvd_right (dvd_mul_left _ _))
  exact k₁.symm.trans k₂

/-- **Primitive forms of discriminant $D$.** The integer triples $(a, b, c)$, standing for the
forms $ax^2 + bxy + cy^2$, with $b^2 - 4ac = D$ and $\gcd(a, b, c) = 1$.

Source: Anthony W. Knapp, *Advanced Algebra*, digital second edition, 2016, Chapter I, §3, p. 12
(forms, discriminant, primitive forms). -/
def PrimitiveForm (D : ℤ) : Type :=
  {f : ℤ × ℤ × ℤ // discrim f.1 f.2.1 f.2.2 = D ∧ Int.gcd (Int.gcd f.1 f.2.1 : ℤ) f.2.2 = 1}

/-- Proper equivalence of primitive forms of discriminant $D$, as a setoid.

Source: Anthony W. Knapp, *Advanced Algebra*, digital second edition, 2016, Chapter I, §3, p. 13
(proper equivalence is an equivalence relation). -/
instance PrimitiveForm.setoid (D : ℤ) : Setoid (PrimitiveForm D) where
  r f g := ProperlyEquivalent f.1 g.1
  iseqv := ⟨fun f => ProperlyEquivalent.refl f.1, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- **Proper equivalence classes of primitive forms of discriminant $D$.** The quotient of the
primitive forms $(a, b, c)$ with $b^2 - 4ac = D$ by proper equivalence.

Source: Anthony W. Knapp, *Advanced Algebra*, digital second edition, 2016, Chapter I, §4,
Theorem 1.12, pp. 27–28 (proper equivalence classes of primitive forms of discriminant $D$). -/
def FormClass (D : ℤ) : Type := Quotient (PrimitiveForm.setoid D)

namespace FormClass

variable {D : ℤ}

/-- The proper equivalence class of the primitive form $(a, b, c)$ of discriminant $D$.

Source: Anthony W. Knapp, *Advanced Algebra*, digital second edition, 2016, Chapter I, §4, Theorem
1.12, p. 27. -/
def mk (a b c : ℤ) (hd : discrim a b c = D) (hp : Int.gcd (Int.gcd a b : ℤ) c = 1) :
    FormClass D :=
  Quotient.mk _ ⟨(a, b, c), hd, hp⟩

/-- Two primitive forms of discriminant $D$ have the same class exactly when they are properly
equivalent.

Source: Anthony W. Knapp, *Advanced Algebra*, digital second edition, 2016, Chapter I, §3, p. 13
(proper equivalence classes). -/
theorem mk_eq_mk_iff {a b c a' b' c' : ℤ} {hd : discrim a b c = D}
    {hp : Int.gcd (Int.gcd a b : ℤ) c = 1} {hd' : discrim a' b' c' = D}
    {hp' : Int.gcd (Int.gcd a' b' : ℤ) c' = 1} :
    mk a b c hd hp = mk a' b' c' hd' hp' ↔ ProperlyEquivalent (a, b, c) (a', b', c') :=
  ⟨Quotient.exact, fun h => Quotient.sound h⟩

/-- Every class is the class of a primitive form of discriminant $D$.

Source: Anthony W. Knapp, *Advanced Algebra*, digital second edition, 2016, Chapter I, §4, Theorem
1.12, p. 27. -/
private theorem exists_mk (x : FormClass D) :
    ∃ (a b c : ℤ) (hd : discrim a b c = D) (hp : Int.gcd (Int.gcd a b : ℤ) c = 1),
      mk a b c hd hp = x := by
  induction x using Quotient.inductionOn with
  | h f =>
    obtain ⟨⟨a, b, c⟩, hd, hp⟩ := f
    exact ⟨a, b, c, hd, hp, rfl⟩

/-- **Aligned representatives of two classes.** For $D$ not a square, any two classes contain
primitive forms $(a_1, b, c_1)$ and $(a_2, b, c_2)$ of discriminant $D$ with $c_1 = j a_2$ and
$c_2 = j a_1$ (aligned forms), and their composition $(a_1 a_2, b, j)$ is primitive of
discriminant $D$.

Source: Anthony W. Knapp, *Advanced Algebra*, digital second edition, 2016, Chapter I, §4, Theorem
1.12(a), p. 27, and Proposition 1.9, p. 25. -/
theorem exists_mul (hD : ¬ IsSquare D) (x y : FormClass D) :
    ∃ z : FormClass D, ∃ (a₁ a₂ b c₁ c₂ j : ℤ) (hd₁ : discrim a₁ b c₁ = D)
      (hp₁ : Int.gcd (Int.gcd a₁ b : ℤ) c₁ = 1) (hd₂ : discrim a₂ b c₂ = D)
      (hp₂ : Int.gcd (Int.gcd a₂ b : ℤ) c₂ = 1) (hd : discrim (a₁ * a₂) b j = D)
      (hp : Int.gcd (Int.gcd (a₁ * a₂) b : ℤ) j = 1),
      mk a₁ b c₁ hd₁ hp₁ = x ∧ mk a₂ b c₂ hd₂ hp₂ = y ∧ c₁ = j * a₂ ∧ c₂ = j * a₁ ∧
        z = mk (a₁ * a₂) b j hd hp := by
  obtain ⟨a, b, c, hd, hp, rfl⟩ := exists_mk x
  obtain ⟨a', b', c', hd', hp', rfl⟩ := exists_mk y
  obtain ⟨a₁, a₂, B, c₁, c₂, j, e₁, e₂, hj₁, hj₂, -, -, -⟩ :=
    exists_aligned (f₁ := (a, b, c)) (f₂ := (a', b', c')) hp hp'
      (by change ¬ IsSquare (discrim a b c); rw [hd]; exact hD) (hd'.trans hd.symm) one_ne_zero
  have hd₁ : discrim a₁ B c₁ = D := e₁.discrim_eq.trans hd
  have hp₁ : Int.gcd (Int.gcd a₁ B : ℤ) c₁ = 1 := e₁.gcd_eq_one hp
  have hp₂ : Int.gcd (Int.gcd a₂ B : ℤ) c₂ = 1 := e₂.gcd_eq_one hp'
  obtain ⟨hpc, hdc, -, -⟩ := composition_of_aligned hp₁ hp₂ hj₁ hj₂
  exact ⟨_, a₁, a₂, B, c₁, c₂, j, hd₁, hp₁, e₂.discrim_eq.trans hd', hp₂, hdc.trans hd₁, hpc,
    (mk_eq_mk_iff.mpr e₁).symm, (mk_eq_mk_iff.mpr e₂).symm, hj₁, hj₂, rfl⟩

/-- **The product of classes.** For $D$ not a square, the product of two classes is the class of
the composition $(a_1 a_2, b, j)$ of aligned representatives: primitive forms $(a_1, b, c_1)$ and
$(a_2, b, c_2)$ of discriminant $D$ in the two classes with $c_1 = j a_2$ and $c_2 = j a_1$, chosen
once and for all (Knapp's Theorem 1.12(a), `exists_aligned`). By `mk_mul_mk` the choice does not
matter.

Source: Anthony W. Knapp, *Advanced Algebra*, digital second edition, 2016, Chapter I, §4,
Theorem 1.12(b), p. 28. -/
noncomputable instance [Fact (¬ IsSquare D)] : Mul (FormClass D) :=
  ⟨fun x y => (exists_mul Fact.out x y).choose⟩

/-- **The product of classes is the class of the composition of any aligned representatives
(Knapp's Theorem 1.12(b)).** For $D$ not a square, if $(a_1, b, c_1)$ and $(a_2, b, c_2)$ are
primitive forms of discriminant $D$ with $c_1 = j a_2$ and $c_2 = j a_1$ (aligned forms in Knapp's
sense), then the product of their classes is the class of their composition $(a_1 a_2, b, j)$.

Source: Anthony W. Knapp, *Advanced Algebra*, digital second edition, 2016, Chapter I, §4,
Theorem 1.12(b), p. 28, with its proof, pp. 28–30. -/
theorem mk_mul_mk [Fact (¬ IsSquare D)] {a₁ a₂ b c₁ c₂ j : ℤ} {hd₁ : discrim a₁ b c₁ = D}
    {hp₁ : Int.gcd (Int.gcd a₁ b : ℤ) c₁ = 1} {hd₂ : discrim a₂ b c₂ = D}
    {hp₂ : Int.gcd (Int.gcd a₂ b : ℤ) c₂ = 1} (hj₁ : c₁ = j * a₂) (hj₂ : c₂ = j * a₁)
    {hd : discrim (a₁ * a₂) b j = D} {hp : Int.gcd (Int.gcd (a₁ * a₂) b : ℤ) j = 1} :
    mk a₁ b c₁ hd₁ hp₁ * mk a₂ b c₂ hd₂ hp₂ = mk (a₁ * a₂) b j hd hp := by
  obtain ⟨A₁, A₂, B, C₁, C₂, J, hD₁, hP₁, hD₂, hP₂, hD₃, hP₃, e₁, e₂, hJ₁, hJ₂, hz⟩ :=
    (exists_mul Fact.out (mk a₁ b c₁ hd₁ hp₁) (mk a₂ b c₂ hd₂ hp₂)).choose_spec
  change (exists_mul Fact.out _ _).choose = _
  rw [hz, mk_eq_mk_iff]
  have hD : ¬ IsSquare (discrim A₁ B C₁) := by
    rw [hD₁]; exact Fact.out
  exact composition_class_well_defined hP₁ hP₂ hD hJ₁ hJ₂ hj₁ hj₂ (mk_eq_mk_iff.mp e₁)
    (mk_eq_mk_iff.mp e₂)

/-- For $D \equiv 0$ or $1 \pmod 4$, the form $(1, \varepsilon, (\varepsilon - D)/4)$ with
$\varepsilon = D \bmod 2$ has discriminant $D$.

Source: Anthony W. Knapp, *Advanced Algebra*, digital second edition, 2016, Chapter I, §4, Theorem
1.12(c), p. 28, and the first paragraph of its proof, p. 30. -/
theorem discrim_one_form (h4 : D % 4 = 0 ∨ D % 4 = 1) :
    discrim 1 (D % 2) ((D % 2 - D) / 4) = D := by
  simp only [discrim]
  rcases Int.emod_two_eq_zero_or_one D with h | h <;> rw [h] <;> omega

/-- A form with first coefficient $1$ is primitive. -/
theorem gcd_one_form (b c : ℤ) : Int.gcd (Int.gcd 1 b : ℤ) c = 1 := by
  simp

/-- **The identity class.** For $D \equiv 0$ or $1 \pmod 4$, the class of the form
$(1, \varepsilon, (\varepsilon - D)/4)$, where $\varepsilon = 0$ if $D \equiv 0 \pmod 4$ and
$\varepsilon = 1$ if $D \equiv 1 \pmod 4$: the class of $(1, 0, -D/4)$ or of $(1, 1, -(D - 1)/4)$.

Source: Anthony W. Knapp, *Advanced Algebra*, digital second edition, 2016, Chapter I, §4,
Theorem 1.12(c), p. 28. -/
instance [h4 : Fact (D % 4 = 0 ∨ D % 4 = 1)] : One (FormClass D) :=
  ⟨mk 1 (D % 2) ((D % 2 - D) / 4) (discrim_one_form h4.out) (gcd_one_form _ _)⟩

/-- For $D \equiv 0$ or $1 \pmod 4$, the identity class is the class of
$(1, \varepsilon, (\varepsilon - D)/4)$, $\varepsilon = D \bmod 2$. -/
theorem one_def [h4 : Fact (D % 4 = 0 ∨ D % 4 = 1)] :
    (1 : FormClass D) = mk 1 (D % 2) ((D % 2 - D) / 4) (discrim_one_form h4.out)
      (gcd_one_form _ _) := rfl

/-- A form $(1, b, c)$ of discriminant $D$ lies in the identity class: it is a translate of
$(1, \varepsilon, (\varepsilon - D)/4)$.

Source: Anthony W. Knapp, *Advanced Algebra*, digital second edition, 2016, Chapter I, §4, the
first paragraph of the proof of Theorem 1.12(c), p. 30. -/
private theorem mk_one_eq_one [h4 : Fact (D % 4 = 0 ∨ D % 4 = 1)] {b c : ℤ} {hd : discrim 1 b c = D}
    {hp : Int.gcd (Int.gcd 1 b : ℤ) c = 1} : mk 1 b c hd hp = 1 := by
  rw [one_def, mk_eq_mk_iff]
  obtain ⟨l, hl⟩ := two_dvd_sub_of_discrim_eq (hd.trans (discrim_one_form h4.out).symm)
  exact (properlyEquivalent_of_eq_add one_ne_zero (l := l) (by linear_combination hl)
    (hd.trans (discrim_one_form h4.out).symm)).symm

/-- **The identity class for the composition of forms.** For $D$ not a square with $D \equiv 0$
or $1 \pmod 4$, the product of any class $\mathcal{C}$ with the class $1$ of
$(1, \varepsilon, (\varepsilon - D)/4)$, $\varepsilon = D \bmod 2$, is $\mathcal{C}$.

Source: Anthony W. Knapp, *Advanced Algebra*, digital second edition, 2016, Chapter I, §4,
Theorem 1.12(c), p. 28, with the first paragraph of its proof, p. 30. -/
theorem mul_identity [Fact (¬ IsSquare D)] [Fact (D % 4 = 0 ∨ D % 4 = 1)] (x : FormClass D) :
    x * 1 = x := by
  obtain ⟨a, b, c, hd, hp, rfl⟩ := exists_mk x
  have hd' : discrim 1 b (a * c) = D := by rw [← hd]; simp only [discrim]; ring
  rw [← mk_one_eq_one (hd := hd') (hp := gcd_one_form _ _),
    mk_mul_mk (j := c) (by ring) (by ring) (hd := by rw [mul_one]; exact hd)
      (hp := by rw [mul_one]; exact hp), mk_eq_mk_iff, mul_one]
  exact .refl _

/-- The forms $(a, b, c)$ and $(a, -b, c)$ have the same discriminant. -/
theorem discrim_neg_middle (a b c : ℤ) : discrim a (-b) c = discrim a b c := by
  simp only [discrim, neg_sq]

/-- The form $(a, -b, c)$ is primitive exactly when $(a, b, c)$ is. -/
theorem gcd_neg_middle (a b c : ℤ) :
    Int.gcd (Int.gcd a (-b) : ℤ) c = Int.gcd (Int.gcd a b : ℤ) c := by
  rw [Int.gcd_neg]

/-- **Inverse classes.** The class of $(a, -b, c)$ for the class of $(a, b, c)$.

Source: Anthony W. Knapp, *Advanced Algebra*, digital second edition, 2016, Chapter I, §4, Theorem
1.12(c), p. 28. -/
instance : Inv (FormClass D) :=
  ⟨Quotient.map (fun f => ⟨(f.1.1, -f.1.2.1, f.1.2.2),
      (discrim_neg_middle _ _ _).trans f.2.1, (gcd_neg_middle _ _ _).trans f.2.2⟩)
    (fun _ _ h => ProperlyEquivalent.neg_middle h)⟩

/-- The inverse of the class of $(a, b, c)$ is the class of $(a, -b, c)$.

Source: Anthony W. Knapp, *Advanced Algebra*, digital second edition, 2016, Chapter I, §4, Theorem
1.12(c), p. 28. -/
theorem inv_mk {a b c : ℤ} {hd : discrim a b c = D} {hp : Int.gcd (Int.gcd a b : ℤ) c = 1} :
    (mk a b c hd hp)⁻¹ = mk a (-b) c ((discrim_neg_middle a b c).trans hd)
      ((gcd_neg_middle a b c).trans hp) := rfl

/-- **Inverse classes for the composition of forms.** For $D$ not a square with $D \equiv 0$ or
$1 \pmod 4$, the product of the classes of a primitive form $(a, b, c)$ of discriminant $D$ and of
$(a, -b, c)$ is the identity class.

Source: Anthony W. Knapp, *Advanced Algebra*, digital second edition, 2016, Chapter I, §4,
Theorem 1.12(c), p. 28, with the second paragraph of its proof, p. 30. -/
theorem mk_mul_mk_neg [Fact (¬ IsSquare D)] [Fact (D % 4 = 0 ∨ D % 4 = 1)] {a b c : ℤ}
    {hd : discrim a b c = D} {hp : Int.gcd (Int.gcd a b : ℤ) c = 1}
    {hd' : discrim a (-b) c = D} {hp' : Int.gcd (Int.gcd a (-b) : ℤ) c = 1} :
    mk a b c hd hp * mk a (-b) c hd' hp' = 1 := by
  have hdc : discrim c b a = D := by rw [← hd]; simp only [discrim]; ring
  have hpc : Int.gcd (Int.gcd c b : ℤ) a = 1 := by
    have := (properlyEquivalent_swap a (-b) c).gcd_eq_one hp'
    rwa [neg_neg] at this
  have e : mk a (-b) c hd' hp' = mk c b a hdc hpc := by
    rw [mk_eq_mk_iff]; simpa using properlyEquivalent_swap a (-b) c
  have hd₁ : discrim 1 (-b) (a * c) = D := by rw [← hd]; simp only [discrim]; ring
  rw [e, mk_mul_mk (j := 1) (by ring) (by ring) (hd := by rw [← hd]; simp only [discrim]; ring)
    (hp := (composition_of_aligned hp hpc (j := 1) (by ring) (by ring)).1),
    ← mk_one_eq_one (hd := hd₁) (hp := gcd_one_form _ _), mk_eq_mk_iff]
  exact properlyEquivalent_swap (a * c) b 1

/-- **Commutativity.** For $D$ not a square, the product of classes is commutative: the
composition of $(a_2, b, c_2)$ and $(a_1, b, c_1)$ is the composition of $(a_1, b, c_1)$ and
$(a_2, b, c_2)$.

Source: Anthony W. Knapp, *Advanced Algebra*, digital second edition, 2016, Chapter I, §4, the
proof of Theorem 1.12(c), p. 30 ("commutativity of multiplication is clear"). -/
protected theorem mul_comm [Fact (¬ IsSquare D)] (x y : FormClass D) : x * y = y * x := by
  obtain ⟨-, a₁, a₂, b, c₁, c₂, j, hd₁, hp₁, hd₂, hp₂, hd, hp, rfl, rfl, hj₁, hj₂, -⟩ :=
    exists_mul Fact.out x y
  rw [mk_mul_mk hj₁ hj₂ (hd := hd) (hp := hp), mk_mul_mk hj₂ hj₁ (hd := by rw [mul_comm]; exact hd)
    (hp := by rw [mul_comm]; exact hp), mk_eq_mk_iff, mul_comm]
  exact .refl _

/-- **Associativity of the composition of classes of forms.** For $D$ not a square, the product
of classes is associative.

Source: Anthony W. Knapp, *Advanced Algebra*, digital second edition, 2016, Chapter I, §4, the
last part of the proof of Theorem 1.12(c), pp. 30–31. -/
protected theorem mul_assoc [Fact (¬ IsSquare D)] (x y z : FormClass D) :
    x * y * z = x * (y * z) := by
  have hD : ¬ IsSquare D := Fact.out
  have hne : ∀ {a b c : ℤ}, discrim a b c = D → a ≠ 0 :=
    fun h => fst_ne_zero_of_not_isSquare (by rw [h]; exact hD)
  obtain ⟨a₁, b₁, c₁, hd₁, hp₁, rfl⟩ := exists_mk x
  obtain ⟨a', b', c', hd', hp', rfl⟩ := exists_mk y
  obtain ⟨a'', b'', c'', hd'', hp'', rfl⟩ := exists_mk z
  -- Knapp's `a₂` prime to `a₁` and `a₃` prime to `a₁ a₂`.
  obtain ⟨x₂, y₂, hxy₂, hg₂⟩ := exists_gcd_eq_one_value hp' (hne hd₁)
  obtain ⟨b₂, c₂, e₂, -⟩ := exists_properlyEquivalent_fst_eq (a', b', c') hxy₂
  set a₂ := a' * x₂ ^ 2 + b' * x₂ * y₂ + c' * y₂ ^ 2
  have hd₂ : discrim a₂ b₂ c₂ = D := e₂.discrim_eq.trans hd'
  obtain ⟨x₃, y₃, hxy₃, hg₃⟩ := exists_gcd_eq_one_value hp'' (mul_ne_zero (hne hd₁) (hne hd₂))
  obtain ⟨b₃, c₃, e₃, -⟩ := exists_properlyEquivalent_fst_eq (a'', b'', c'') hxy₃
  set a₃ := a'' * x₃ ^ 2 + b'' * x₃ * y₃ + c'' * y₃ ^ 2
  have hd₃ : discrim a₃ b₃ c₃ = D := e₃.discrim_eq.trans hd''
  have h₁₂ : IsCoprime a₁ a₂ := Int.isCoprime_iff_gcd_eq_one.mpr hg₂
  have h₁₂₃ : IsCoprime (a₁ * a₂) a₃ := Int.isCoprime_iff_gcd_eq_one.mpr hg₃
  -- A common middle coefficient `B ≡ bⱼ (mod 2aⱼ)`.
  obtain ⟨B₀, hB₀₁, hB₀₂⟩ := exists_modEq_two_mul h₁₂
    (two_dvd_sub_of_discrim_eq (hd₂.trans hd₁.symm))
  obtain ⟨B, hB, hB₃⟩ := exists_modEq_two_mul h₁₂₃ (b₁ := B₀) (b₂ := b₃) (by
    obtain ⟨t, ht⟩ := (Int.ModEq.of_mul_right a₁ hB₀₁ :
      B₀ ≡ b₁ [ZMOD 2]).symm.dvd
    obtain ⟨u, hu⟩ := two_dvd_sub_of_discrim_eq (hd₃.trans hd₁.symm)
    exact ⟨u - t, by linear_combination hu - ht⟩)
  have hB₁ : B ≡ b₁ [ZMOD 2 * a₁] :=
    (Int.ModEq.of_dvd ⟨a₂, by ring⟩ hB).trans hB₀₁
  have hB₂ : B ≡ b₂ [ZMOD 2 * a₂] :=
    (Int.ModEq.of_dvd ⟨a₁, by ring⟩ hB).trans hB₀₂
  have hsq : ∀ {a b c : ℤ}, discrim a b c = D → ¬ IsSquare (discrim a b c) :=
    fun h => by rw [h]; exact hD
  obtain ⟨-, -, hT₁, E₁⟩ := translate (hsq hd₁) hB₁
  obtain ⟨-, -, hT₂, E₂⟩ := translate (hsq hd₂) hB₂
  obtain ⟨-, -, hT₃, E₃⟩ := translate (hsq hd₃) hB₃
  set C₁ := (B ^ 2 - discrim a₁ b₁ c₁) / (4 * a₁)
  set C₂ := (B ^ 2 - discrim a₂ b₂ c₂) / (4 * a₂)
  set C₃ := (B ^ 2 - discrim a₃ b₃ c₃) / (4 * a₃)
  have hD₁ : discrim a₁ B C₁ = D := hT₁.trans hd₁
  have hD₂ : discrim a₂ B C₂ = D := hT₂.trans hd₂
  have hD₃ : discrim a₃ B C₃ = D := hT₃.trans hd₃
  have hP₁ := E₁.gcd_eq_one hp₁
  have hP₂ := E₂.gcd_eq_one (e₂.gcd_eq_one hp')
  have hP₃ := E₃.gcd_eq_one (e₃.gcd_eq_one hp'')
  have k₁ : mk a₁ b₁ c₁ hd₁ hp₁ = mk a₁ B C₁ hD₁ hP₁ := mk_eq_mk_iff.mpr E₁
  have k₂ : mk a' b' c' hd' hp' = mk a₂ B C₂ hD₂ hP₂ := mk_eq_mk_iff.mpr (e₂.trans E₂)
  have k₃ : mk a'' b'' c'' hd'' hp'' = mk a₃ B C₃ hD₃ hP₃ := mk_eq_mk_iff.mpr (e₃.trans E₃)
  rw [k₁, k₂, k₃]
  have h₂₃ : Int.gcd a₂ a₃ = 1 :=
    Int.isCoprime_iff_gcd_eq_one.mp h₁₂₃.of_mul_left_right
  have h₁₂' : Int.gcd a₁ a₂ = 1 := hg₂
  obtain ⟨-, -, j₁₂, hj₁, hj₂⟩ := exists_eq_mul_of_gcd_eq_one (hsq hD₁) (hD₂.trans hD₁.symm) h₁₂'
  obtain ⟨-, -, j₂₃, hj₂', hj₃⟩ := exists_eq_mul_of_gcd_eq_one (hsq hD₂) (hD₃.trans hD₂.symm) h₂₃
  obtain ⟨hp₁₂, hd₁₂', -, -⟩ := composition_of_aligned hP₁ hP₂ hj₁ hj₂
  obtain ⟨hp₂₃, hd₂₃', -, -⟩ := composition_of_aligned hP₂ hP₃ hj₂' hj₃
  have hd₁₂ : discrim (a₁ * a₂) B j₁₂ = D := hd₁₂'.trans hD₁
  have hd₂₃ : discrim (a₂ * a₃) B j₂₃ = D := hd₂₃'.trans hD₂
  rw [mk_mul_mk hj₁ hj₂ (hd := hd₁₂) (hp := hp₁₂), mk_mul_mk hj₂' hj₃ (hd := hd₂₃) (hp := hp₂₃)]
  obtain ⟨-, -, j, hj₁₂, hj₃'⟩ := exists_eq_mul_of_gcd_eq_one (hsq hd₁₂) (hD₃.trans hd₁₂.symm)
    (Int.isCoprime_iff_gcd_eq_one.mp h₁₂₃)
  obtain ⟨-, -, j', hj₁', hj₂₃⟩ := exists_eq_mul_of_gcd_eq_one (hsq hD₁) (hd₂₃.trans hD₁.symm)
    (Int.isCoprime_iff_gcd_eq_one.mp (h₁₂.mul_right h₁₂₃.of_mul_left_left))
  obtain ⟨hpL, hdL, -, -⟩ := composition_of_aligned hp₁₂ hP₃ hj₁₂ hj₃'
  obtain ⟨hpR, hdR, -, -⟩ := composition_of_aligned hP₁ hp₂₃ hj₁' hj₂₃
  rw [mk_mul_mk hj₁₂ hj₃' (hd := hdL.trans hd₁₂) (hp := hpL),
    mk_mul_mk hj₁' hj₂₃ (hd := hdR.trans hD₁) (hp := hpR), mk_eq_mk_iff]
  have hjj : j = j' := eq_of_discrim_eq (a := a₁ * a₂ * a₃) (b := B)
    (mul_ne_zero (mul_ne_zero (hne hd₁) (hne hd₂)) (hne hd₃))
    (by rw [hdL.trans hd₁₂, mul_assoc, hdR.trans hD₁])
  rw [hjj, mul_assoc]
  exact .refl _

/-- **The form class group (Knapp's Theorem 1.12(c)).** For an integer $D$ that is not a square,
with $D \equiv 0$ or $1 \pmod 4$, the proper equivalence classes of primitive forms of
discriminant $D$ form an abelian group under the product of classes (`mk_mul_mk`). Its identity is
the class of $(1, \varepsilon, (\varepsilon - D)/4)$, $\varepsilon = D \bmod 2$ (`one_def`), and the
inverse of the class of $(a, b, c)$ is the class of $(a, -b, c)$ (`inv_mk`).

Finiteness, which Knapp also states, is not part of this instance.

Source: Anthony W. Knapp, *Advanced Algebra*, digital second edition, 2016, Chapter I, §4,
Theorem 1.12(c), p. 28, with its proof, pp. 30–31. -/
noncomputable instance instCommGroup [Fact (¬ IsSquare D)] [Fact (D % 4 = 0 ∨ D % 4 = 1)] :
    CommGroup (FormClass D) where
  mul_assoc := FormClass.mul_assoc
  one_mul x := by rw [FormClass.mul_comm, mul_identity]
  mul_one := mul_identity
  inv_mul_cancel x := by
    obtain ⟨a, b, c, hd, hp, rfl⟩ := exists_mk x
    rw [inv_mk, FormClass.mul_comm, mk_mul_mk_neg]
  mul_comm := FormClass.mul_comm

/-- **The form class group of a negative discriminant.** For $D < 0$ (not a square, with
$D \equiv 0$ or $1 \pmod 4$), the classes of positive definite forms, those containing a form
$(a, b, c)$ with $a > 0$, form a subgroup of the group of classes of primitive forms of
discriminant $D$. Knapp defines the form class group of $D < 0$ to be this subgroup.

Source: Anthony W. Knapp, *Advanced Algebra*, digital second edition, 2016, Chapter I, §4, the
remark after Theorem 1.12, p. 28; positive definite forms, §3, p. 14. -/
def posDefSubgroup (D : ℤ) [Fact (¬ IsSquare D)] [Fact (D % 4 = 0 ∨ D % 4 = 1)] (hD : D < 0) :
    Subgroup (FormClass D) where
  carrier := {x | ∃ (a b c : ℤ) (hd : discrim a b c = D)
    (hp : Int.gcd (Int.gcd a b : ℤ) c = 1), 0 < a ∧ mk a b c hd hp = x}
  mul_mem' := by
    rintro _ _ ⟨a, b, c, hd, hp, ha, rfl⟩ ⟨a', b', c', hd', hp', ha', rfl⟩
    obtain ⟨a₁, a₂, B, c₁, c₂, j, e₁, e₂, hj₁, hj₂, -, -, -⟩ :=
      exists_aligned (f₁ := (a, b, c)) (f₂ := (a', b', c')) hp hp'
        (by change ¬ IsSquare (discrim a b c); rw [hd]; exact Fact.out) (hd'.trans hd.symm)
        one_ne_zero
    have hd₁ : discrim a₁ B c₁ = D := e₁.discrim_eq.trans hd
    have hp₁ := e₁.gcd_eq_one hp
    have hp₂ := e₂.gcd_eq_one hp'
    have ha₁ : 0 < a₁ := (e₁.fst_pos_iff (by rw [show discrim a b c = D from hd]; exact hD)).mpr ha
    have ha₂ : 0 < a₂ :=
      (e₂.fst_pos_iff (by rw [show discrim a' b' c' = D from hd']; exact hD)).mpr ha'
    obtain ⟨hpc, hdc, -, -⟩ := composition_of_aligned hp₁ hp₂ hj₁ hj₂
    refine ⟨a₁ * a₂, B, j, hdc.trans hd₁, hpc, mul_pos ha₁ ha₂, ?_⟩
    rw [(mk_eq_mk_iff.mpr e₁ : mk a b c hd hp = mk a₁ B c₁ hd₁ hp₁),
      (mk_eq_mk_iff.mpr e₂ : mk a' b' c' hd' hp' = mk a₂ B c₂ (e₂.discrim_eq.trans hd') hp₂),
      mk_mul_mk hj₁ hj₂]
  one_mem' := ⟨1, _, _, _, _, one_pos, rfl⟩
  inv_mem' := by
    rintro _ ⟨a, b, c, hd, hp, ha, rfl⟩
    exact ⟨a, -b, c, _, _, ha, inv_mk.symm⟩

/-- For $D < 0$, the class of a primitive form $(a, b, c)$ of discriminant $D$ lies in the
positive definite subgroup exactly when $a > 0$.

Source: Anthony W. Knapp, *Advanced Algebra*, digital second edition, 2016, Chapter I, §3, p. 14
(a form equivalent to a positive definite form is positive definite). -/
theorem mk_mem_posDefSubgroup [Fact (¬ IsSquare D)] [Fact (D % 4 = 0 ∨ D % 4 = 1)] (hD : D < 0)
    {a b c : ℤ} {hd : discrim a b c = D} {hp : Int.gcd (Int.gcd a b : ℤ) c = 1} :
    mk a b c hd hp ∈ posDefSubgroup D hD ↔ 0 < a := by
  refine ⟨?_, fun ha => ⟨a, b, c, hd, hp, ha, rfl⟩⟩
  rintro ⟨a', b', c', hd', hp', ha', e⟩
  have hneg : discrim a' b' c' < 0 := by rw [hd']; exact hD
  exact ((mk_eq_mk_iff.mp e).fst_pos_iff hneg).mpr ha'

end FormClass

end BinaryQuadraticForm
