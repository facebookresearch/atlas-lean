/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.QuadraticForms.RootLattice
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Data.Nat.PrimeFin
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Translates, aligned forms and their composition

For integer triples $(a, b, c)$, standing for the binary quadratic forms $ax^2 + bxy + cy^2$, with
proper equivalence `BinaryQuadraticForm.ProperlyEquivalent` given by substitutions in
$\mathrm{SL}_2(\mathbb{Z})$, this file proves the elementary steps of Knapp's construction of the
form class group (*Advanced Algebra*, Chapter I, §§3–4):

* `BinaryQuadraticForm.properlyEquivalent_invariants`: proper equivalence is an equivalence
  relation preserving the discriminant, primitivity and, for a negative discriminant, positive
  definiteness;
* `BinaryQuadraticForm.translate`: a translate $(a, b', (b'^2 - D)/(4a))$, $b' \equiv b \pmod{2a}$,
  of a form $(a, b, c)$ of nonsquare discriminant $D$ is a form properly equivalent to it;
* `BinaryQuadraticForm.ProperlyEquivalent.mul_fst_div_snd` (Knapp's Lemma 1.11): moving a common
  factor of the last coefficients of properly equivalent forms to the first coefficients;
* `BinaryQuadraticForm.exists_properlyEquivalent_fst_eq`: an integer primitively represented by a
  form is the first coefficient of a properly equivalent form;
* `BinaryQuadraticForm.exists_gcd_eq_one_value` (Knapp's Lemma 1.10): a primitive form
  primitively represents an integer prime to any given nonzero integer;
* `BinaryQuadraticForm.exists_eq_mul_of_gcd_eq_one`: forms of one nonsquare discriminant with the
  same middle coefficient and coprime first coefficients are aligned;
* `BinaryQuadraticForm.composition_of_aligned` (Knapp's Proposition 1.9): the composition
  $(a_1 a_2, b, j)$ of aligned forms is primitive of the same discriminant;
* `BinaryQuadraticForm.exists_aligned` (Knapp's Theorem 1.12(a)): two classes of primitive forms of
  a nonsquare discriminant contain aligned forms whose first coefficients are prime to each other
  and to a given nonzero integer.

The source is Anthony W. Knapp, *Advanced Algebra*, digital second edition, published by the
author, East Setauket, NY, 2016, Chapter I, §3, pp. 12–14 and 18, and §4, pp. 25–28.
-/

@[expose] public section

open scoped MatrixGroups

namespace BinaryQuadraticForm

/-- The matrix $\begin{pmatrix} p & q \\ r & s \end{pmatrix}$ of determinant $ps - qr = 1$. -/
private def slOfDet (p q r s : ℤ) (h : p * s - q * r = 1) : SL(2, ℤ) :=
  ⟨!![p, q; r, s], by rw [Matrix.det_fin_two_of]; exact h⟩

private theorem det_entries (γ : SL(2, ℤ)) : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
  have := γ.det_coe
  rwa [Matrix.det_fin_two] at this

/-- **Proper equivalence by explicit substitutions.** The form $g$ is properly equivalent to $f$
exactly when $g(x, y) = f(px + qy, rx + sy)$ for integers $p, q, r, s$ with $ps - qr = 1$, that is,
when the coefficients of $g$ are
$(ap^2 + bpr + cr^2,\ 2apq + b(ps + qr) + 2crs,\ aq^2 + bqs + cs^2)$ for $f = (a, b, c)$.

Source: Anthony W. Knapp, *Advanced Algebra*, digital second edition, 2016, Chapter I, §3, p. 12
(the change of variables by $\begin{pmatrix} \alpha & \beta \\ \gamma & \delta \end{pmatrix}$ and
the coefficients of the new form) and p. 13 (proper equivalence classes are the orbits of
$\mathrm{SL}(2, \mathbb{Z})$). -/
theorem properlyEquivalent_iff_exists {f g : ℤ × ℤ × ℤ} :
    ProperlyEquivalent f g ↔ ∃ p q r s : ℤ, p * s - q * r = 1 ∧
      g = (f.1 * p ^ 2 + f.2.1 * p * r + f.2.2 * r ^ 2,
        2 * f.1 * p * q + f.2.1 * (p * s + q * r) + 2 * f.2.2 * r * s,
        f.1 * q ^ 2 + f.2.1 * q * s + f.2.2 * s ^ 2) := by
  constructor
  · rintro ⟨γ, rfl⟩
    exact ⟨γ 0 0, γ 0 1, γ 1 0, γ 1 1, det_entries γ, rfl⟩
  · rintro ⟨p, q, r, s, h, rfl⟩
    exact ⟨slOfDet p q r s h, by simp [substitute, slOfDet]⟩

/-- A form properly equivalent to a primitive form is primitive. -/
theorem ProperlyEquivalent.gcd_eq_one {f g : ℤ × ℤ × ℤ} (h : ProperlyEquivalent f g)
    (hf : Int.gcd (Int.gcd f.1 f.2.1 : ℤ) f.2.2 = 1) :
    Int.gcd (Int.gcd g.1 g.2.1 : ℤ) g.2.2 = 1 := by
  obtain ⟨γ, rfl⟩ := h
  exact gcd_substitute hf γ

/-- Of two properly equivalent forms of negative discriminant, one has positive first coefficient
exactly when the other has. -/
theorem ProperlyEquivalent.fst_pos_iff {f g : ℤ × ℤ × ℤ} (h : ProperlyEquivalent f g)
    (hD : discrim f.1 f.2.1 f.2.2 < 0) : 0 < g.1 ↔ 0 < f.1 := by
  have hD' : discrim g.1 g.2.1 g.2.2 < 0 := h.discrim_eq ▸ hD
  constructor
  · intro hg
    obtain ⟨γ, rfl⟩ := h.symm
    exact substitute_fst_pos hg hD' γ
  · intro hf
    obtain ⟨γ, rfl⟩ := h
    exact substitute_fst_pos hf hD γ

/-- **Proper equivalence preserves the discriminant, primitivity and positive definiteness.** For
integer triples $(a, b, c)$, standing for the forms $ax^2 + bxy + cy^2$:

1. proper equivalence is an equivalence relation;
2. properly equivalent forms have the same discriminant $b^2 - 4ac$;
3. a form properly equivalent to a primitive form ($\gcd(a, b, c) = 1$) is primitive;
4. if $(a, b, c)$ and $(a', b', c')$ are properly equivalent and their discriminant is negative,
   then $a' > 0$ if and only if $a > 0$.

Source: Anthony W. Knapp, *Advanced Algebra*, digital second edition, 2016, Chapter I, §3: p. 13,
(i)–(iii) (the identity matrix acts as the identity, a product of matrices acts as the two
substitutions in turn, and each member of $\mathrm{GL}(2, \mathbb{Z})$ preserves the discriminant;
proper equivalence classes are the orbits of $\mathrm{SL}(2, \mathbb{Z})$), and p. 14 (for $D < 0$
"any form equivalent to a positive definite form is again positive definite"). Knapp assumes
throughout §3 that forms are primitive (p. 12); item 3 records that proper equivalence keeps
primitivity. -/
theorem properlyEquivalent_invariants :
    Equivalence ProperlyEquivalent ∧
      (∀ {f g : ℤ × ℤ × ℤ}, ProperlyEquivalent f g →
        discrim g.1 g.2.1 g.2.2 = discrim f.1 f.2.1 f.2.2) ∧
      (∀ {f g : ℤ × ℤ × ℤ}, ProperlyEquivalent f g →
        Int.gcd (Int.gcd f.1 f.2.1 : ℤ) f.2.2 = 1 → Int.gcd (Int.gcd g.1 g.2.1 : ℤ) g.2.2 = 1) ∧
      (∀ {f g : ℤ × ℤ × ℤ}, ProperlyEquivalent f g → discrim f.1 f.2.1 f.2.2 < 0 →
        (0 < g.1 ↔ 0 < f.1)) :=
  ⟨properlyEquivalent_equivalence, fun h => h.discrim_eq, fun h => h.gcd_eq_one,
    fun h => h.fst_pos_iff⟩

/-- **The first coefficient of a form of nonsquare discriminant is not zero.** If the discriminant
$b^2 - 4ac$ of $(a, b, c)$ is not the square of an integer, then $a \ne 0$.

Source: Anthony W. Knapp, *Advanced Algebra*, digital second edition, 2016, Chapter I, §3, p. 14:
"Since $D = b^2 - 4ac$ is assumed not to be the square of an integer, neither $a$ nor $c$ can
be $0$." -/
theorem fst_ne_zero_of_not_isSquare {a b c : ℤ} (hD : ¬ IsSquare (discrim a b c)) : a ≠ 0 := by
  rintro rfl
  exact hD ⟨b, by simp [discrim, sq]⟩

/-- **The substitution of a translate.** For integers $a, b, c, l$, the substitution
$(x, y) \mapsto (x + ly, y)$ carries $(a, b, c)$ to the properly equivalent form
$(a, b + 2al, al^2 + bl + c)$.

Source: Anthony W. Knapp, *Advanced Algebra*, digital second edition, 2016, Chapter I, §4, p. 26,
the paragraph before Lemma 1.10: the computation with
$\begin{pmatrix} 1 & l \\ 0 & 1 \end{pmatrix}$, "valid for any integer $l$". -/
theorem properlyEquivalent_translate (a b c l : ℤ) :
    ProperlyEquivalent (a, b, c) (a, b + 2 * a * l, a * l ^ 2 + b * l + c) :=
  properlyEquivalent_iff_exists.mpr ⟨1, l, 0, 1, by ring, by
    simp only [Prod.mk.injEq]
    exact ⟨by ring, by ring, by ring⟩⟩

/-- **A translate of a form is properly equivalent to it.** Let $(a, b, c)$ be a form whose
discriminant $D = b^2 - 4ac$ is not the square of an integer, so that $a \ne 0$. If $b'$ is an
integer with $b' \equiv b \pmod{2a}$, then $4a$ divides $b'^2 - D$, the form
$(a, b', c')$ with $c' = (b'^2 - D)/(4a)$ (a translate of $(a, b, c)$) has discriminant $D$, and
it is properly equivalent to $(a, b, c)$.

Source: Anthony W. Knapp, *Advanced Algebra*, digital second edition, 2016, Chapter I, §4, p. 26,
the paragraph before Lemma 1.10 ("the number $c' = (b'^2 - D)/(4a)$ is an integer", "the
translate $(a, b', c')$ is properly equivalent to $(a, b, c)$"), and §3, p. 14 ($a \ne 0$). -/
theorem translate {a b c b' : ℤ} (hD : ¬ IsSquare (discrim a b c)) (hb : b' ≡ b [ZMOD 2 * a]) :
    a ≠ 0 ∧ 4 * a ∣ b' ^ 2 - discrim a b c ∧
      discrim a b' ((b' ^ 2 - discrim a b c) / (4 * a)) = discrim a b c ∧
      ProperlyEquivalent (a, b, c) (a, b', (b' ^ 2 - discrim a b c) / (4 * a)) := by
  have ha := fst_ne_zero_of_not_isSquare hD
  obtain ⟨l, hl⟩ : 2 * a ∣ b' - b := Int.ModEq.dvd hb.symm
  have hb' : b' = b + 2 * a * l := by linear_combination hl
  have key : b' ^ 2 - discrim a b c = 4 * a * (a * l ^ 2 + b * l + c) := by
    rw [hb']
    simp only [discrim]
    ring
  have h4 : (4 : ℤ) * a ≠ 0 := mul_ne_zero (by norm_num) ha
  have hc : (b' ^ 2 - discrim a b c) / (4 * a) = a * l ^ 2 + b * l + c := by
    rw [key]
    exact Int.mul_ediv_cancel_left _ h4
  refine ⟨ha, ⟨_, key⟩, ?_, ?_⟩
  · rw [hc, hb']
    simp only [discrim]
    ring
  · rw [hc, hb']
    exact properlyEquivalent_translate a b c l

/-- **Moving a common factor of the last coefficients of properly equivalent forms (Knapp's
Lemma 1.11).** Let $(a_1, b, c_1)$ and $(a_2, b, c_2)$ be properly equivalent forms. If $l$ is an
integer with $\gcd(a_1, a_2, l) = 1$ that divides $c_1$ and $c_2$, then $(l a_1, b, c_1 / l)$ and
$(l a_2, b, c_2 / l)$ are properly equivalent forms.

Knapp states the lemma for forms of nonsquare discriminant (then $l \ne 0$, as $c_1 \ne 0$); the
proof does not use that hypothesis, which is left out here. When $l = 0$ both forms are
$(0, b, 0)$.

Source: Anthony W. Knapp, *Advanced Algebra*, digital second edition, 2016, Chapter I, §4,
Lemma 1.11 with its proof, p. 27. -/
theorem ProperlyEquivalent.mul_fst_div_snd {a₁ a₂ b c₁ c₂ l : ℤ}
    (h : ProperlyEquivalent (a₁, b, c₁) (a₂, b, c₂)) (hl : Int.gcd (Int.gcd a₁ a₂ : ℤ) l = 1)
    (hl₁ : l ∣ c₁) (hl₂ : l ∣ c₂) :
    ProperlyEquivalent (l * a₁, b, c₁ / l) (l * a₂, b, c₂ / l) := by
  rcases eq_or_ne l 0 with rfl | hl0
  · obtain rfl := zero_dvd_iff.mp hl₁
    obtain rfl := zero_dvd_iff.mp hl₂
    simpa using ProperlyEquivalent.refl ((0 : ℤ), b, (0 : ℤ))
  obtain ⟨p, q, r, s, hdet, he⟩ := properlyEquivalent_iff_exists.mp h
  simp only [Prod.mk.injEq] at he
  obtain ⟨ha₂, hb, hc₂⟩ := he
  have hE : a₁ * p * q + b * q * r + c₁ * r * s = 0 := by
    have h2 : 2 * (a₁ * p * q + b * q * r + c₁ * r * s) = 0 := by
      linear_combination (-1 : ℤ) * hb - b * hdet
    exact (mul_eq_zero.mp h2).resolve_left two_ne_zero
  -- Knapp's equations `a₂ β + c₁ γ = 0` and `a₁ β + c₂ γ = 0`.
  have h₁ : a₂ * q + c₁ * r = 0 := by linear_combination q * ha₂ + p * hE - c₁ * r * hdet
  have h₂ : a₁ * q + c₂ * r = 0 := by linear_combination r * hc₂ + s * hE - a₁ * q * hdet
  have hlq : l ∣ q := by
    have d₁ : l ∣ a₁ * q := by
      obtain ⟨t, rfl⟩ := hl₂
      exact ⟨-(t * r), by linear_combination h₂⟩
    have d₂ : l ∣ a₂ * q := by
      obtain ⟨t, rfl⟩ := hl₁
      exact ⟨-(t * r), by linear_combination h₁⟩
    have e : (Int.gcd a₁ a₂ : ℤ) * q = Int.gcdA a₁ a₂ * (a₁ * q) + Int.gcdB a₁ a₂ * (a₂ * q) := by
      rw [Int.gcd_eq_gcd_ab]
      ring
    have hg : l ∣ (Int.gcd a₁ a₂ : ℤ) * q := by
      rw [e]
      exact dvd_add (dvd_mul_of_dvd_right d₁ _) (dvd_mul_of_dvd_right d₂ _)
    have hcop : IsCoprime l (Int.gcd a₁ a₂ : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]
      exact hl
    exact hcop.dvd_of_dvd_mul_left hg
  obtain ⟨q', rfl⟩ := hlq
  obtain ⟨c₁', rfl⟩ := hl₁
  obtain ⟨c₂', rfl⟩ := hl₂
  rw [Int.mul_ediv_cancel_left c₁' hl0, Int.mul_ediv_cancel_left c₂' hl0]
  refine properlyEquivalent_iff_exists.mpr ⟨p, q', l * r, s, by linear_combination hdet, ?_⟩
  simp only [Prod.mk.injEq]
  refine ⟨by linear_combination l * ha₂, by linear_combination hb, ?_⟩
  exact mul_left_cancel₀ hl0 (by linear_combination hc₂)

/-- **A primitively represented integer is the first coefficient of a properly equivalent form.**
Let $f = (a, b, c)$ be a form and let $x_0, y_0$ be integers with $\gcd(x_0, y_0) = 1$, and put
$n = a x_0^2 + b x_0 y_0 + c y_0^2$. Then there are integers $b'$ and $c'$ such that $(n, b', c')$
is properly equivalent to $(a, b, c)$, and $(n, b', c')$ has the discriminant of $(a, b, c)$.

Source: Anthony W. Knapp, *Advanced Algebra*, digital second edition, 2016, Chapter I, §3, p. 18,
the proof of uniqueness in Theorem 1.6(b) (a matrix of determinant $1$ with first column
$(x_0, y_0)$ carries the form to one taking the represented value at $(1, 0)$), and §4, p. 28, the
proof of Theorem 1.12(a), which applies this argument to arbitrary primitively represented
integers. -/
theorem exists_properlyEquivalent_fst_eq (f : ℤ × ℤ × ℤ) {x₀ y₀ : ℤ} (h : Int.gcd x₀ y₀ = 1) :
    ∃ b' c' : ℤ,
      ProperlyEquivalent f (f.1 * x₀ ^ 2 + f.2.1 * x₀ * y₀ + f.2.2 * y₀ ^ 2, b', c') ∧
      discrim (f.1 * x₀ ^ 2 + f.2.1 * x₀ * y₀ + f.2.2 * y₀ ^ 2) b' c' =
        discrim f.1 f.2.1 f.2.2 := by
  have hb : x₀ * Int.gcdA x₀ y₀ + y₀ * Int.gcdB x₀ y₀ = 1 := by
    have := Int.gcd_eq_gcd_ab x₀ y₀
    rw [h] at this
    exact_mod_cast this.symm
  have hpe := (properlyEquivalent_iff_exists (f := f)).mpr
    ⟨x₀, -Int.gcdB x₀ y₀, y₀, Int.gcdA x₀ y₀, by linear_combination hb, rfl⟩
  exact ⟨_, _, hpe, hpe.discrim_eq⟩

private theorem dvd_gcd_three {k : ℕ} {a b c : ℤ} (ha : (k : ℤ) ∣ a) (hb : (k : ℤ) ∣ b)
    (hc : (k : ℤ) ∣ c) : k ∣ Int.gcd (Int.gcd a b : ℤ) c :=
  Int.dvd_gcd (Int.natCast_dvd_natCast.mpr (Int.dvd_gcd ha hb)) hc

/-- **A primitive form primitively represents an integer prime to any given nonzero integer
(Knapp's Lemma 1.10).** Let $(a, b, c)$ be a primitive form, $\gcd(a, b, c) = 1$, and let $m \ne 0$
be an integer. Then there are integers $x_0$ and $y_0$ with $\gcd(x_0, y_0) = 1$ and
$\gcd(m, a x_0^2 + b x_0 y_0 + c y_0^2) = 1$.

Knapp states the lemma for forms of nonsquare discriminant; his proof (the products $x_0$ of the
primes dividing $a$ and $m$ but not $c$, and $y_0$ of the primes dividing $m$ but not $a$) does not
use that hypothesis, which is left out here.

Source: Anthony W. Knapp, *Advanced Algebra*, digital second edition, 2016, Chapter I, §4,
Lemma 1.10 with its proof, p. 26; primitive representation is defined in §3, p. 14. -/
theorem exists_gcd_eq_one_value {a b c m : ℤ} (hprim : Int.gcd (Int.gcd a b : ℤ) c = 1)
    (hm : m ≠ 0) :
    ∃ x₀ y₀ : ℤ, Int.gcd x₀ y₀ = 1 ∧ Int.gcd m (a * x₀ ^ 2 + b * x₀ * y₀ + c * y₀ ^ 2) = 1 := by
  classical
  set S := m.natAbs.primeFactors with hS
  set TX := S.filter (fun p : ℕ => (p : ℤ) ∣ a ∧ ¬ (p : ℤ) ∣ c) with hTX
  set TY := S.filter (fun p : ℕ => ¬ (p : ℤ) ∣ a) with hTY
  set X : ℕ := ∏ p ∈ TX, p with hX
  set Y : ℕ := ∏ p ∈ TY, p with hY
  have mem : ∀ {T : Finset ℕ}, T ⊆ S → ∀ {p : ℕ}, p.Prime → (p ∣ ∏ q ∈ T, q ↔ p ∈ T) := by
    intro T hT p hp
    constructor
    · intro hd
      obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp hd
      have hq' : q.Prime := Nat.prime_of_mem_primeFactors (hT hq)
      rwa [(Nat.prime_dvd_prime_iff_eq hp hq').mp hpq]
    · intro hpT
      exact Finset.dvd_prod_of_mem _ hpT
  have hXiff : ∀ {p : ℕ}, p.Prime → p ∈ S → ((p : ℤ) ∣ (X : ℤ) ↔ (p : ℤ) ∣ a ∧ ¬ (p : ℤ) ∣ c) := by
    intro p hp hpS
    rw [Int.natCast_dvd_natCast, hX, mem (Finset.filter_subset _ _) hp, Finset.mem_filter]
    exact and_iff_right hpS
  have hYiff : ∀ {p : ℕ}, p.Prime → p ∈ S → ((p : ℤ) ∣ (Y : ℤ) ↔ ¬ (p : ℤ) ∣ a) := by
    intro p hp hpS
    rw [Int.natCast_dvd_natCast, hY, mem (Finset.filter_subset _ _) hp, Finset.mem_filter]
    exact and_iff_right hpS
  refine ⟨X, Y, ?_, ?_⟩
  · rw [Int.gcd_natCast_natCast]
    refine Nat.coprime_of_dvd fun k hk hkX hkY => ?_
    have h₁ := (mem (Finset.filter_subset _ _) hk).mp hkX
    have h₂ := (mem (Finset.filter_subset _ _) hk).mp hkY
    exact (Finset.mem_filter.mp h₂).2 (Finset.mem_filter.mp h₁).2.1
  · rw [Int.gcd_eq_natAbs]
    refine Nat.coprime_of_dvd fun k hk hkm hkv => ?_
    have hkS : k ∈ S := Nat.mem_primeFactors.mpr ⟨hk, hkm, Int.natAbs_ne_zero.mpr hm⟩
    have hpk : Prime (k : ℤ) := Nat.prime_iff_prime_int.mp hk
    have hv : (k : ℤ) ∣ a * X ^ 2 + b * X * Y + c * Y ^ 2 := Int.natCast_dvd.mpr hkv
    have not_one : ¬ (k : ℤ) ∣ ((1 : ℕ) : ℤ) := fun h =>
      hk.not_dvd_one (Int.natCast_dvd_natCast.mp h)
    by_cases ha : (k : ℤ) ∣ a
    · by_cases hc : (k : ℤ) ∣ c
      · have nX : ¬ (k : ℤ) ∣ (X : ℤ) := fun h => ((hXiff hk hkS).mp h).2 hc
        have nY : ¬ (k : ℤ) ∣ (Y : ℤ) := fun h => (hYiff hk hkS).mp h ha
        have hbXY : (k : ℤ) ∣ b * X * Y := by
          have e : b * X * Y = (a * X ^ 2 + b * X * Y + c * Y ^ 2) - a * X ^ 2 - c * Y ^ 2 := by
            ring
          rw [e]
          exact dvd_sub (dvd_sub hv (dvd_mul_of_dvd_left ha _)) (dvd_mul_of_dvd_left hc _)
        have hb : (k : ℤ) ∣ b := by
          rcases hpk.dvd_or_dvd hbXY with h | h
          · rcases hpk.dvd_or_dvd h with h | h
            · exact h
            · exact absurd h nX
          · exact absurd h nY
        apply not_one
        rw [← hprim]
        exact Int.natCast_dvd_natCast.mpr (dvd_gcd_three ha hb hc)
      · have hXk : (k : ℤ) ∣ (X : ℤ) := (hXiff hk hkS).mpr ⟨ha, hc⟩
        have nY : ¬ (k : ℤ) ∣ (Y : ℤ) := fun h => (hYiff hk hkS).mp h ha
        have hcY : (k : ℤ) ∣ c * Y ^ 2 := by
          have e : c * Y ^ 2 = (a * X ^ 2 + b * X * Y + c * Y ^ 2) - a * X ^ 2 - b * X * Y := by
            ring
          rw [e]
          exact dvd_sub (dvd_sub hv (dvd_mul_of_dvd_left ha _))
            (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hXk _) _)
        rcases hpk.dvd_or_dvd hcY with h | h
        · exact hc h
        · exact nY (hpk.dvd_of_dvd_pow h)
    · have hYk : (k : ℤ) ∣ (Y : ℤ) := (hYiff hk hkS).mpr ha
      have nX : ¬ (k : ℤ) ∣ (X : ℤ) := fun h => ha ((hXiff hk hkS).mp h).1
      have haX : (k : ℤ) ∣ a * X ^ 2 := by
        have e : a * X ^ 2 = (a * X ^ 2 + b * X * Y + c * Y ^ 2) - b * X * Y - c * Y ^ 2 := by
          ring
        rw [e]
        exact dvd_sub (dvd_sub hv (dvd_mul_of_dvd_right hYk _))
          (dvd_mul_of_dvd_right (dvd_pow hYk two_ne_zero) _)
      rcases hpk.dvd_or_dvd haX with h | h
      · exact ha h
      · exact nX (hpk.dvd_of_dvd_pow h)

/-- **Forms with coprime first coefficients and equal middle coefficients are aligned.** Let
$(a_1, b, c_1)$ and $(a_2, b, c_2)$ be forms of the same discriminant $D$, not the square of an
integer, with the same middle coefficient $b$ and with $\gcd(a_1, a_2) = 1$. Then $a_1 \ne 0$,
$a_2 \ne 0$, and the rational number $c_1 / a_2 = c_2 / a_1$ is an integer $j$: $c_1 = j a_2$ and
$c_2 = j a_1$.

Source: Anthony W. Knapp, *Advanced Algebra*, digital second edition, 2016, Chapter I, §4, p. 25,
the paragraph after Proposition 1.9 ("the rational number $j$ is automatically an integer if
$\mathrm{GCD}(a_1, a_2) = 1$"), and §3, p. 14 ($a \ne 0$ for a nonsquare discriminant). -/
theorem exists_eq_mul_of_gcd_eq_one {a₁ a₂ b c₁ c₂ : ℤ} (hD : ¬ IsSquare (discrim a₁ b c₁))
    (hdisc : discrim a₂ b c₂ = discrim a₁ b c₁) (h : Int.gcd a₁ a₂ = 1) :
    a₁ ≠ 0 ∧ a₂ ≠ 0 ∧ ∃ j : ℤ, c₁ = j * a₂ ∧ c₂ = j * a₁ := by
  have ha₁ := fst_ne_zero_of_not_isSquare hD
  have ha₂ : a₂ ≠ 0 := fst_ne_zero_of_not_isSquare (hdisc ▸ hD)
  have hac : a₁ * c₁ = a₂ * c₂ := by
    simp only [discrim] at hdisc
    have h4 : (4 : ℤ) * (a₁ * c₁) = 4 * (a₂ * c₂) := by linear_combination hdisc
    exact mul_left_cancel₀ (by norm_num) h4
  have hcop : IsCoprime a₁ a₂ := Int.isCoprime_iff_gcd_eq_one.mpr h
  obtain ⟨j, hj⟩ : a₁ ∣ c₂ := hcop.dvd_of_dvd_mul_left ⟨c₁, hac.symm⟩
  refine ⟨ha₁, ha₂, j, ?_, by rw [hj]; ring⟩
  apply mul_left_cancel₀ ha₁
  rw [hac, hj]
  ring

/-- **Composition of aligned forms (Knapp's Proposition 1.9).** Let $(a_1, b, c_1)$ and
$(a_2, b, c_2)$ be primitive forms with the same middle coefficient that are aligned: there is an
integer $j$ with $c_1 = j a_2$ and $c_2 = j a_1$, that is, $j = c_1 / a_2 = c_2 / a_1$. Then their
composition $(a_1 a_2, b, j)$ is primitive with the discriminant $b^2 - 4 a_1 c_1$ of the two
forms,
$$(a_1 x_1^2 + b x_1 y_1 + c_1 y_1^2)(a_2 x_2^2 + b x_2 y_2 + c_2 y_2^2)
  = a_1 a_2 X^2 + b X Y + j Y^2$$
with $X = x_1 x_2 - j y_1 y_2$ and $Y = a_1 x_1 y_2 + a_2 x_2 y_1 + b y_1 y_2$, for all integers
$x_1, y_1, x_2, y_2$, and if $a_1 > 0$ and $a_2 > 0$ then $a_1 a_2 > 0$.

Knapp states the proposition for forms of the same nonsquare discriminant; with $c_1 = j a_2$ and
$c_2 = j a_1$ the forms automatically have the same discriminant, and the conclusions do not need
it to be a nonsquare. The positivity clause is Knapp's remark after Theorem 1.12, p. 28: the
composition of aligned positive definite forms is positive definite.

Source: Anthony W. Knapp, *Advanced Algebra*, digital second edition, 2016, Chapter I, §4,
Proposition 1.9 with its proof and the definition of aligned forms, p. 25, and the remark after
Theorem 1.12, p. 28. -/
theorem composition_of_aligned {a₁ a₂ b c₁ c₂ j : ℤ}
    (hp₁ : Int.gcd (Int.gcd a₁ b : ℤ) c₁ = 1) (hp₂ : Int.gcd (Int.gcd a₂ b : ℤ) c₂ = 1)
    (hj₁ : c₁ = j * a₂) (hj₂ : c₂ = j * a₁) :
    Int.gcd (Int.gcd (a₁ * a₂) b : ℤ) j = 1 ∧ discrim (a₁ * a₂) b j = discrim a₁ b c₁ ∧
      (∀ x₁ y₁ x₂ y₂ : ℤ,
        (a₁ * x₁ ^ 2 + b * x₁ * y₁ + c₁ * y₁ ^ 2) * (a₂ * x₂ ^ 2 + b * x₂ * y₂ + c₂ * y₂ ^ 2) =
          a₁ * a₂ * (x₁ * x₂ - j * y₁ * y₂) ^ 2 +
            b * (x₁ * x₂ - j * y₁ * y₂) * (a₁ * x₁ * y₂ + a₂ * x₂ * y₁ + b * y₁ * y₂) +
            j * (a₁ * x₁ * y₂ + a₂ * x₂ * y₁ + b * y₁ * y₂) ^ 2) ∧
      (0 < a₁ → 0 < a₂ → 0 < a₁ * a₂) := by
  refine ⟨?_, ?_, ?_, fun h₁ h₂ => mul_pos h₁ h₂⟩
  · by_contra hne
    obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hne
    have hpg' : (p : ℤ) ∣ (Int.gcd (Int.gcd (a₁ * a₂) b : ℤ) j : ℤ) :=
      Int.natCast_dvd_natCast.mpr hpg
    have h12 : (p : ℤ) ∣ (Int.gcd (a₁ * a₂) b : ℤ) := hpg'.trans (Int.gcd_dvd_left _ _)
    have hA : (p : ℤ) ∣ a₁ * a₂ := h12.trans (Int.gcd_dvd_left _ _)
    have hB : (p : ℤ) ∣ b := h12.trans (Int.gcd_dvd_right _ _)
    have hJ : (p : ℤ) ∣ j := hpg'.trans (Int.gcd_dvd_right _ _)
    have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    rcases hpp.dvd_or_dvd hA with h | h
    · have := dvd_gcd_three h hB (hj₁ ▸ dvd_mul_of_dvd_left hJ a₂)
      rw [hp₁] at this
      exact hp.not_dvd_one this
    · have := dvd_gcd_three h hB (hj₂ ▸ dvd_mul_of_dvd_left hJ a₁)
      rw [hp₂] at this
      exact hp.not_dvd_one this
  · rw [hj₁]
    simp only [discrim]
    ring
  · intro x₁ y₁ x₂ y₂
    rw [hj₁, hj₂]
    ring

/-- **Two classes of primitive forms contain aligned forms (Knapp's Theorem 1.12(a)).** Let
$f_1$ and $f_2$ be primitive forms of the same discriminant $D$, not the square of an integer, and
let $m \ne 0$ be an integer. Then there are forms $(a_1, b, c_1)$ properly equivalent to $f_1$ and
$(a_2, b, c_2)$ properly equivalent to $f_2$, with the same middle coefficient, that are aligned
($c_1 = j a_2$ and $c_2 = j a_1$ for an integer $j$), with $\gcd(a_1, a_2) = 1$,
$\gcd(a_1, m) = 1$ and $\gcd(a_2, m) = 1$.

The proper equivalence classes of $f_1$ and $f_2$ are Knapp's classes $\mathcal{C}_1$ and
$\mathcal{C}_2$; their members are primitive of discriminant $D$ by
`properlyEquivalent_invariants`.

Source: Anthony W. Knapp, *Advanced Algebra*, digital second edition, 2016, Chapter I, §4,
Theorem 1.12(a), p. 27, with its proof, p. 28. -/
theorem exists_aligned {f₁ f₂ : ℤ × ℤ × ℤ}
    (hp₁ : Int.gcd (Int.gcd f₁.1 f₁.2.1 : ℤ) f₁.2.2 = 1)
    (hp₂ : Int.gcd (Int.gcd f₂.1 f₂.2.1 : ℤ) f₂.2.2 = 1)
    (hD : ¬ IsSquare (discrim f₁.1 f₁.2.1 f₁.2.2))
    (hdisc : discrim f₂.1 f₂.2.1 f₂.2.2 = discrim f₁.1 f₁.2.1 f₁.2.2) {m : ℤ} (hm : m ≠ 0) :
    ∃ a₁ a₂ b c₁ c₂ j : ℤ, ProperlyEquivalent f₁ (a₁, b, c₁) ∧
      ProperlyEquivalent f₂ (a₂, b, c₂) ∧ c₁ = j * a₂ ∧ c₂ = j * a₁ ∧
      Int.gcd a₁ a₂ = 1 ∧ Int.gcd a₁ m = 1 ∧ Int.gcd a₂ m = 1 := by
  obtain ⟨x, y, hxy, hm₁⟩ := exists_gcd_eq_one_value hp₁ hm
  obtain ⟨b₁, c₁', he₁, hd₁⟩ := exists_properlyEquivalent_fst_eq f₁ hxy
  set A₁ := f₁.1 * x ^ 2 + f₁.2.1 * x * y + f₁.2.2 * y ^ 2 with hA₁
  have hA₁0 : A₁ ≠ 0 := fst_ne_zero_of_not_isSquare (b := b₁) (c := c₁') (by rw [hd₁]; exact hD)
  obtain ⟨x', y', hxy', hm₂⟩ := exists_gcd_eq_one_value hp₂ (mul_ne_zero hm hA₁0)
  obtain ⟨b₂, c₂', he₂, hd₂⟩ := exists_properlyEquivalent_fst_eq f₂ hxy'
  set A₂ := f₂.1 * x' ^ 2 + f₂.2.1 * x' * y' + f₂.2.2 * y' ^ 2 with hA₂
  have hc₂ : IsCoprime (m * A₁) A₂ := Int.isCoprime_iff_gcd_eq_one.mpr hm₂
  have hcopA : IsCoprime A₁ A₂ := hc₂.of_mul_left_right
  have hcopm : IsCoprime m A₂ := hc₂.of_mul_left_left
  -- `b₂ - b₁` is even.
  obtain ⟨u₁, hu₁⟩ := Int.even_mul_pred_self b₁
  obtain ⟨u₂, hu₂⟩ := Int.even_mul_pred_self b₂
  set t := 2 * (A₂ * c₂' - A₁ * c₁') - u₂ + u₁ with ht_def
  have ht : b₂ - b₁ = 2 * t := by
    simp only [discrim] at hd₁ hd₂ hdisc
    linear_combination -hu₂ + hu₁ + hd₂ - hd₁ + hdisc
  obtain ⟨u, v, huv⟩ := hcopA
  have T₁ := properlyEquivalent_translate A₁ b₁ c₁' (u * t)
  have T₂ := properlyEquivalent_translate A₂ b₂ c₂' (-(v * t))
  have hbb : b₂ + 2 * A₂ * -(v * t) = b₁ + 2 * A₁ * (u * t) := by
    linear_combination ht - 2 * t * huv
  rw [hbb] at T₂
  have E₁ := he₁.trans T₁
  have E₂ := he₂.trans T₂
  set b := b₁ + 2 * A₁ * (u * t)
  set C₁ := A₁ * (u * t) ^ 2 + b₁ * (u * t) + c₁'
  set C₂ := A₂ * (-(v * t)) ^ 2 + b₂ * -(v * t) + c₂'
  have hD₁ : discrim A₁ b C₁ = discrim f₁.1 f₁.2.1 f₁.2.2 := E₁.discrim_eq
  have hD₂ : discrim A₂ b C₂ = discrim f₂.1 f₂.2.1 f₂.2.2 := E₂.discrim_eq
  have hgA : Int.gcd A₁ A₂ = 1 :=
    Int.isCoprime_iff_gcd_eq_one.mp ⟨u, v, huv⟩
  obtain ⟨-, -, j, hj₁, hj₂⟩ := exists_eq_mul_of_gcd_eq_one (b := b) (c₁ := C₁) (c₂ := C₂)
    (by rw [hD₁]; exact hD) (by rw [hD₂, hD₁, hdisc]) hgA
  exact ⟨A₁, A₂, b, C₁, C₂, j, E₁, E₂, hj₁, hj₂, hgA, by rw [Int.gcd_comm]; exact hm₁,
    Int.isCoprime_iff_gcd_eq_one.mp hcopm.symm⟩

end BinaryQuadraticForm
