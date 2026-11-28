/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Data.Int.Basic
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Characteristic numbers in the generalized Markov tree

For a middle Farey fraction strictly between zero and one, the characteristic number satisfies
the positive-sign congruence modulo the middle generalized Markov number.

## References

* Yasuaki Gyoda and Shuhei Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
  Are Prime Powers*, INTEGERS 26 (2026), Article A91, pp. 1–27, Sections 1.2, 2 and 4.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Generalized Markov triple.** For a natural number $k$, a $k$-generalized Markov triple
is a triple $(a, b, c)$ of positive integers satisfying the $k$-generalized Markov equation
$\mathrm{GME}(k)$:
$$a^2 + b^2 + c^2 + k(bc + ca + ab) = (3 + 3k)abc.$$
For $k = 0$ these are the classical Markov triples.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 1.2. -/
public def IsGenMarkovTriple (k a b c : ℕ) : Prop :=
  0 < a ∧ 0 < b ∧ 0 < c ∧
    a ^ 2 + b ^ 2 + c ^ 2 + k * (b * c + c * a + a * b) = (3 + 3 * k) * a * b * c

/-- **$(1, 1, 1)$ is a generalized Markov triple.** For every natural number $k$, the triple
$(1, 1, 1)$ is a $k$-generalized Markov triple.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 1.2. -/
public theorem isGenMarkovTriple_one_one_one (k : ℕ) : IsGenMarkovTriple k 1 1 1 := by
  refine ⟨Nat.one_pos, Nat.one_pos, Nat.one_pos, ?_⟩
  ring

/-- **The Markov triple $(1, 1, 2)$.** The triple $(1, 1, 2)$ is a $0$-generalized Markov
triple, that is, a classical Markov triple: $1^2 + 1^2 + 2^2 = 3 \cdot 1 \cdot 1 \cdot 2$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 1.1. -/
public theorem isGenMarkovTriple_zero_one_one_two : IsGenMarkovTriple 0 1 1 2 := by
  refine ⟨Nat.one_pos, Nat.one_pos, Nat.two_pos, ?_⟩
  norm_num

/-- **Vieta jumping of generalized Markov triples.** For a natural number $k$, the left Vieta
jumping sends a triple $(a, b, c)$ of natural numbers to
$(a, \lfloor (a^2 + kab + b^2)/c \rfloor, b)$ and the right Vieta jumping sends it to
$(b, \lfloor (b^2 + kbc + c^2)/a \rfloor, c)$, where division by $0$ gives $0$. The left jumping
is indexed by the boolean value false and the right one by true.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 2. -/
public def genMarkovVieta (k : ℕ) : Bool → ℕ × ℕ × ℕ → ℕ × ℕ × ℕ
  | false, (a, b, c) => (a, (a ^ 2 + k * a * b + b ^ 2) / c, b)
  | true, (a, b, c) => (b, (b ^ 2 + k * b * c + c ^ 2) / a, c)

/-- **Left Vieta jumping.** For natural numbers $k,a,b,c$, the left Vieta jumping of
$(a,b,c)$ is $(a, \lfloor (a^2 + kab + b^2)/c \rfloor, b)$, where division by $0$ gives $0$. -/
public theorem genMarkovVieta_false (k a b c : ℕ) :
    genMarkovVieta k false (a, b, c) = (a, (a ^ 2 + k * a * b + b ^ 2) / c, b) := rfl

/-- **Right Vieta jumping.** For natural numbers $k,a,b,c$, the right Vieta jumping of
$(a,b,c)$ is $(b, \lfloor (b^2 + kbc + c^2)/a \rfloor, c)$, where division by $0$ gives $0$. -/
public theorem genMarkovVieta_true (k a b c : ℕ) :
    genMarkovVieta k true (a, b, c) = (b, (b ^ 2 + k * b * c + c ^ 2) / a, c) := rfl

/-- **The wide generalized Markov tree.** Fix a natural number $k$. The wide $k$-generalized
Markov tree $\mathrm{WMT}(k)$ is the binary tree of triples of natural numbers with root
$(1, 1, 1)$ in which a vertex $(a, b, c)$ has left child
$(a, \lfloor (a^2 + kab + b^2)/c \rfloor, b)$ and right child
$(b, \lfloor (b^2 + kbc + c^2)/a \rfloor, c)$, the left and right Vieta jumpings. For a path $w$,
a finite sequence of left and right steps, the vertex of $\mathrm{WMT}(k)$ at $w$ is the triple
reached from the root by taking the steps of $w$ in order; the empty path gives the root.

The quotients are divisions of natural numbers, rounded down, with division by $0$ giving $0$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 2. -/
public def wideGenMarkovTree (k : ℕ) (w : List Bool) : ℕ × ℕ × ℕ :=
  w.foldl (fun t d => genMarkovVieta k d t) (1, 1, 1)

/-- **Generalized Markov tree.** For a natural number $k$ and a finite sequence $w$ of left and
right steps, the vertex of the $k$-generalized Markov tree $MT(k)$ at $w$ is the vertex of the
wide $k$-generalized Markov tree $WMT(k)$ reached from its root by one left step followed by the
steps of $w$ in order. Thus $MT(k)$ is the full subtree of $WMT(k)$ rooted at the left child of
the root.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 2. -/
public def genMarkovTree (k : ℕ) (w : List Bool) : ℕ × ℕ × ℕ :=
  wideGenMarkovTree k (false :: w)

/-- **Children in the wide generalized Markov tree are Vieta jumpings.** For every natural
number $k$, every path $w$ and every direction $d$ (left or right), the vertex of the wide
$k$-generalized Markov tree $\mathrm{WMT}(k)$ at the path $w$ followed by one step in direction
$d$ is the image of the vertex at $w$ under the Vieta jumping in direction $d$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 2. -/
public theorem wideGenMarkovTree_append_singleton (k : ℕ) (w : List Bool) (d : Bool) :
    wideGenMarkovTree k (w ++ [d]) = genMarkovVieta k d (wideGenMarkovTree k w) := by
  simp [wideGenMarkovTree, List.foldl_append]

/-- **Root of the generalized Markov tree.** For every natural number $k$, the root of the
$k$-generalized Markov tree $MT(k)$, its vertex at the empty path, is $(1, k + 2, 1)$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 4. -/
public theorem genMarkovTree_nil (k : ℕ) : genMarkovTree k [] = (1, k + 2, 1) := by
  simp only [genMarkovTree, wideGenMarkovTree, List.foldl_cons, List.foldl_nil, genMarkovVieta]
  congr 2
  rw [Nat.div_one]
  ring

/-- **Left child of the root of the classical Markov tree.** For $k = 0$, the vertex of the
Markov tree $MT(0)$ reached from the root by one left step is $(1, 5, 2)$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 2. -/
public theorem genMarkovTree_zero_false : genMarkovTree 0 [false] = (1, 5, 2) := by
  decide

/-- **The Farey tree.** Write a fraction $n/d$, with $n$ and $d$ natural numbers, for the pair
$(n, d)$, so that $1/0$ stands for $\infty$. The Farey tree $\mathrm{FT}$ is the infinite binary
tree of triples of fractions with root $(0/1, 1/1, 1/0)$ in which a vertex $(a/b, c/d, e/f)$
has left child $(a/b, (a+c)/(b+d), c/d)$ and right child $(c/d, (c+e)/(d+f), e/f)$. For a path
$w$, a finite sequence of left and right moves, this gives the vertex of $\mathrm{FT}$ reached
from the root by making the moves of $w$ in order.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 3.2. -/
public def fareyTree (w : List Bool) : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ) :=
  w.foldl (fun T d => match d, T with
    | false, (x, y, _) => (x, (x.1 + y.1, x.2 + y.2), y)
    | true, (_, y, z) => (y, (y.1 + z.1, y.2 + z.2), z)) ((0, 1), (1, 1), (1, 0))

/-- **Left child of the root of the Farey tree.** The left child of the root $(0/1, 1/1, 1/0)$
of the Farey tree is $(0/1, 1/2, 1/1)$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 4. -/
public theorem fareyTree_false : fareyTree [false] = ((0, 1), (1, 2), (1, 1)) := by
  decide

/-- **Characteristic number.** For natural numbers $m_r$, $m_t$, $m_s$, a natural number $x$ is
a characteristic number of $(m_r, m_t, m_s)$ when $0 < x < m_t/2$ and
$m_r x \equiv \pm m_s \pmod{m_t}$, that is, $m_t$ divides $m_r x - m_s$ or $m_r x + m_s$ in
$\mathbb{Z}$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Definition 4.3. -/
public def IsGenMarkovCharNumber (mr mt ms x : ℕ) : Prop :=
  0 < x ∧ 2 * x < mt ∧ ((mt : ℤ) ∣ mr * x - ms ∨ (mt : ℤ) ∣ mr * x + ms)

/-- **Characteristic number of $(1, 5, 2)$.** The number $2$ is a characteristic number of
$(m_r, m_t, m_s) = (1, 5, 2)$: indeed $0 < 2 < 5/2$ and $1 \cdot 2 \equiv 2 \pmod 5$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Definition 4.3. -/
public theorem isGenMarkovCharNumber_one_five_two : IsGenMarkovCharNumber 1 5 2 2 := by
  refine ⟨by norm_num, by norm_num, Or.inl ⟨0, by norm_num⟩⟩

end

namespace genMarkovCharNumber_dvd_sub

-- The endpoints carry fractions p/a and q/c in [0, 1/2]. Their cross difference
-- is the opposite Markov number d. Splitting this interval constructs the desired residue.
private def Edge (a c d : ℕ) : Prop :=
  IsCoprime (a : ℤ) c ∧ ∃ p q : ℤ, 0 ≤ p ∧ 2 * q ≤ c ∧ a * q - c * p = d

private def Vertex (k : ℕ) (t : ℕ × ℕ × ℕ) : Prop :=
  IsGenMarkovTriple k t.1 t.2.1 t.2.2 ∧ Edge t.1 t.2.1 t.2.2 ∧ Edge t.2.1 t.2.2 t.1

-- The opposite entries are the two roots of the Markov equation in its middle variable.
private theorem vieta_product {k a d c : ℕ} (h : IsGenMarkovTriple k a d c) :
    let b := (a ^ 2 + k * a * c + c ^ 2) / d
    b * d = a ^ 2 + k * a * c + c ^ 2 ∧ IsGenMarkovTriple k a b c := by
  obtain ⟨ha, hd, hc, he⟩ := h
  intro b
  have hsum : a ^ 2 + k * a * c + c ^ 2 + (d + k * (a + c)) * d =
      (3 + 3 * k) * a * c * d := by linarith only [he]
  have hdiv : d ∣ a ^ 2 + k * a * c + c ^ 2 := by
    apply (Nat.dvd_add_iff_left (dvd_mul_left d (d + k * (a + c)))).mpr
    rw [hsum]
    exact dvd_mul_left ..
  have hprod : b * d = a ^ 2 + k * a * c + c ^ 2 := Nat.div_mul_cancel hdiv
  have hroots : b + d + k * (a + c) = (3 + 3 * k) * a * c := by
    apply mul_right_cancel₀ hd.ne'
    linarith only [hprod, hsum]
  refine ⟨hprod, ha, ?_, hc, ?_⟩
  · apply Nat.pos_of_mul_pos_right (b := d)
    rw [hprod]
    positivity
  · linarith only [congrArg (b * ·) hroots, hprod]

private theorem vertex_of_edge {k a d c : ℕ} (h : IsGenMarkovTriple k a d c) (edge : Edge a c d) :
    Vertex k (a, (a ^ 2 + k * a * c + c ^ 2) / d, c) := by
  let b := (a ^ 2 + k * a * c + c ^ 2) / d
  obtain ⟨hprod, ht⟩ : b * d = a ^ 2 + k * a * c + c ^ 2 ∧ IsGenMarkovTriple k a b c :=
    vieta_product h
  obtain ⟨cop, p, q, hp, hq, hdet⟩ := edge
  have he : (b : ℤ) * d = (a : ℤ) ^ 2 + k * a * c + (c : ℤ) ^ 2 := by exact_mod_cast hprod
  -- Multiplying by c clears the congruence for the new numerator v. Coprimality cancels c.
  have hdiv : (a : ℤ) ∣ b * p + c := by
    apply cop.dvd_of_dvd_mul_left
    refine ⟨(b : ℤ) * q - a - k * c, ?_⟩
    linear_combination -(b : ℤ) * hdet - he
  obtain ⟨v, hv⟩ := hdiv
  have hleft : (a : ℤ) * v - b * p = c := by linarith only [hv]
  have ha : (0 : ℤ) < a := by exact_mod_cast ht.1
  have hb : (0 : ℤ) < b := by exact_mod_cast ht.2.1
  have hc : (0 : ℤ) < c := by exact_mod_cast ht.2.2.1
  have hright : (b : ℤ) * q - c * (v + k) = a := by
    apply mul_left_cancel₀ ha.ne'
    linear_combination (b : ℤ) * hdet + he - (c : ℤ) * hleft
  have hvpos : 0 < v := by
    apply pos_of_mul_pos_right (a := (a : ℤ)) _ ha.le
    linarith only [hleft, hc, mul_nonneg hb.le hp]
  have hvbound : 2 * v ≤ b := by
    apply le_of_mul_le_mul_right (a := (c : ℤ)) _ hc
    linarith only [hright, ha, mul_le_mul_of_nonneg_left hq hb.le,
      mul_nonneg hc.le (Int.natCast_nonneg k)]
  obtain ⟨x, y, hxy⟩ := cop
  refine ⟨ht, ⟨⟨x + y * v, -y * p, ?_⟩, p, v, hp, hvbound, hleft⟩,
    ⟨⟨x * q, y - x * (v + k), ?_⟩, v + k, q, by positivity, hq, hright⟩⟩
  · linear_combination hxy + y * hleft
  · linear_combination hxy + x * hright

private theorem Vertex.step {k : ℕ} {t : ℕ × ℕ × ℕ} (h : Vertex k t) (direction : Bool) :
    Vertex k (genMarkovVieta k direction t) := by
  obtain ⟨a, b, c⟩ := t
  obtain ⟨⟨ha, hb, hc, he⟩, hl, hr⟩ := h
  cases direction with
  | false => exact vertex_of_edge ⟨ha, hc, hb, by linarith only [he]⟩ hl
  | true => exact vertex_of_edge ⟨hb, ha, hc, by linarith only [he]⟩ hr

private theorem vertex_left_subtree (k : ℕ) (w : List Bool) :
    Vertex k (genMarkovTree k (false :: w)) := by
  have root : IsGenMarkovTriple k 1 1 (k + 2) := ⟨by decide, by decide, by omega, by ring⟩
  have edge : Edge 1 (k + 2) 1 := ⟨isCoprime_one_left, 0, 1, by decide, by omega, by simp⟩
  change Vertex k (w.foldl _ (genMarkovVieta k false (genMarkovTree k [])))
  rw [genMarkovTree_nil]
  exact w.foldlRecOn _ (vertex_of_edge root edge) fun _ h dir _ => h.step dir

private theorem fareyTree_right_den_le_num (w : List Bool) :
    (fareyTree (true :: w)).2.1.2 ≤ (fareyTree (true :: w)).2.1.1 := by
  let P (t : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) :=
    t.1.2 ≤ t.1.1 ∧ t.2.1.2 ≤ t.2.1.1 ∧ t.2.2.2 ≤ t.2.2.1
  suffices h : P (fareyTree (true :: w)) from h.2.1
  unfold fareyTree
  rw [List.foldl_cons]
  apply w.foldlRecOn (motive := P) _ (by decide)
  rintro ⟨a, b, c⟩ ⟨ha, hb, hc⟩ dir _
  cases dir
  · exact ⟨ha, Nat.add_le_add ha hb, hb⟩
  · exact ⟨hb, Nat.add_le_add hb hc, hc⟩

private theorem Vertex.dvd_sub {k a b c u : ℕ} (h : Vertex k (a, b, c))
    (hu : IsGenMarkovCharNumber a b c u) : (b : ℤ) ∣ a * u - c := by
  obtain ⟨ht, ⟨cop, p, q, hp, hq, he⟩, _⟩ := h
  obtain ⟨hu, hbound, hpos | hneg⟩ := hu
  · exact hpos
  · exfalso
    have hd : (b : ℤ) ∣ a * (u + q) := by
      obtain ⟨z, hz⟩ := hneg
      refine ⟨z + p, ?_⟩
      linear_combination hz + he
    have hsum := cop.symm.dvd_of_dvd_mul_left hd
    have ha : (0 : ℤ) < a := by exact_mod_cast ht.1
    have hc : (0 : ℤ) < c := by exact_mod_cast ht.2.2.1
    have hqpos : 0 < q := by
      apply pos_of_mul_pos_right (a := (a : ℤ)) _ ha.le
      linarith only [he, hc, mul_nonneg (Int.natCast_nonneg b) hp]
    have hu' : (0 : ℤ) < u := by exact_mod_cast hu
    have hb' : 2 * (u : ℤ) < b := by exact_mod_cast hbound
    have := Int.le_of_dvd (add_pos hu' hqpos) hsum
    linarith only [this, hq, hb']

end genMarkovCharNumber_dvd_sub

open genMarkovCharNumber_dvd_sub in
/-- **The characteristic number solves $m_r x \equiv m_s \pmod{m_t}$.** Let $k \in \mathbb{N}$,
let $w$ be a finite sequence of left and right moves, let $(r, t, s)$ be the vertex of the
Farey tree at $w$, and let $(m_r, m_t, m_s)$ be the vertex of the $k$-generalized Markov tree
$\mathrm{MT}(k)$ at $w$. Write $t = n/d$. If $0 < n < d$ and $u$ is a characteristic number
of $(m_r, m_t, m_s)$, then $m_t$ divides $m_r u - m_s$ in $\mathbb{Z}$, that is,
$m_r u \equiv m_s \pmod{m_t}$.

Of the two congruences $m_r x \equiv \pm m_s \pmod{m_t}$ allowed in the definition of a
characteristic number, the one with the plus sign holds.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Corollary 4.6. -/
public theorem genMarkovCharNumber_dvd_sub (k : ℕ) (w : List Bool)
    (ht : 0 < (fareyTree w).2.1.1) (ht1 : (fareyTree w).2.1.1 < (fareyTree w).2.1.2) (u : ℕ)
    (hu : IsGenMarkovCharNumber (genMarkovTree k w).1 (genMarkovTree k w).2.1
      (genMarkovTree k w).2.2 u) :
    ((genMarkovTree k w).2.1 : ℤ) ∣ (genMarkovTree k w).1 * u - (genMarkovTree k w).2.2 := by
  cases w with
  | nil => exact (Nat.lt_irrefl _ ht1).elim
  | cons dir w =>
    cases dir
    · exact Vertex.dvd_sub (vertex_left_subtree k w) hu
    · exact (Nat.not_lt_of_ge (fareyTree_right_den_le_num w) ht1).elim

open genMarkovCharNumber_dvd_sub in
/-- **The characteristic number solves $x^2 + kx + 1 \equiv 0 \pmod{m_t}$.** Let
$k \in \mathbb{N}$, let $w$ be a finite sequence of left and right moves, let $(r, t, s)$ be
the vertex of the Farey tree at $w$, and let $(m_r, m_t, m_s)$ be the vertex of the
$k$-generalized Markov tree $\mathrm{MT}(k)$ at $w$. Write $t = n/d$. If $0 < n < d$ and $u$
is a characteristic number of $(m_r, m_t, m_s)$, then $m_t$ divides $u^2 + ku + 1$, that is,
$u^2 + ku + 1 \equiv 0 \pmod{m_t}$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Lemma 4.7. -/
public theorem genMarkovCharNumber_sq_add (k : ℕ) (w : List Bool)
    (ht : 0 < (fareyTree w).2.1.1) (ht1 : (fareyTree w).2.1.1 < (fareyTree w).2.1.2) (u : ℕ)
    (hu : IsGenMarkovCharNumber (genMarkovTree k w).1 (genMarkovTree k w).2.1
      (genMarkovTree k w).2.2 u) :
    (genMarkovTree k w).2.1 ∣ u ^ 2 + k * u + 1 := by
  cases w with
  | nil => exact (Nat.lt_irrefl _ ht1).elim
  | cons dir w =>
    cases dir
    · have hsub := genMarkovCharNumber_dvd_sub k (false :: w) ht ht1 u hu
      have hv := vertex_left_subtree k w
      generalize genMarkovTree k (false :: w) = t at hv hsub ⊢
      obtain ⟨a, b, c⟩ := t
      obtain ⟨⟨_, _, _, he⟩, ⟨cop, _⟩, _⟩ := hv
      have he' : (a : ℤ) ^ 2 + (b : ℤ) ^ 2 + (c : ℤ) ^ 2 +
          k * ((b : ℤ) * c + (c : ℤ) * a + (a : ℤ) * b) = (3 + 3 * (k : ℤ)) * a * b * c := by
        exact_mod_cast he
      have hmarkov : (b : ℤ) ∣ (a : ℤ) ^ 2 + k * a * c + (c : ℤ) ^ 2 := by
        refine ⟨(3 + 3 * (k : ℤ)) * a * c - b - k * (c + (a : ℤ)), ?_⟩
        linear_combination he'
      -- Replacing c by a * u changes the polynomial by a multiple of b.
      have hdiff : (b : ℤ) ∣ (a * (u : ℤ) - c) * (a * (u : ℤ) + c + k * a) :=
        dvd_mul_of_dvd_left hsub _
      have hscaled : (b : ℤ) ∣ (a : ℤ) * (a * ((u : ℤ) ^ 2 + k * u + 1)) := by
        obtain ⟨x, hx⟩ := hmarkov
        obtain ⟨y, hy⟩ := hdiff
        exact ⟨x + y, by linear_combination hx + hy⟩
      have hquad := cop.symm.dvd_of_dvd_mul_left (cop.symm.dvd_of_dvd_mul_left hscaled)
      exact_mod_cast hquad
    · exact (Nat.not_lt_of_ge (fareyTree_right_den_le_num w) ht1).elim

end MetaMathlibExt
