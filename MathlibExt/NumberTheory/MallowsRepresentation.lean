/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Nth
public import Mathlib.NumberTheory.Real.Irrational

/-!
# The Mallows representation of the irrational numbers

We formalize the run-end characterization of the middle letter in Takanori Hida,
*The Mallows Representation of the Irrational Numbers*, INTEGERS 25 (2025), Article A78, Lemma 4.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **The Mallows alphabet.** The letters of Mallows representations are the three distinct
letters $L$, $M$ and $R$, standing for "left", "middle" and "right".

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Definition 4. -/
inductive MallowsLetter
  | L
  | M
  | R
  deriving DecidableEq

/-- **Stern–Brocot letters.** The alphabet of Stern–Brocot representations: the two letters
$L$ ("left") and $R$ ("right").

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Definition 2. -/
inductive SternBrocotLetter
  | L
  | R
  deriving DecidableEq

/-- **The parity alphabet.** The parity alphabet consists of the four letters $O_L$, $E_R$, $O_R$
and $E_L$. The intermediate set $I$ linking the Stern–Brocot and Mallows representations is a set
of infinite sequences over this alphabet.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Section 3. -/
inductive MallowsParityLetter
  | OL
  | ER
  | OR
  | EL
  deriving DecidableEq

/-- **Real value of a fraction encoded as a pair.** The pair $(n, m)$ of natural numbers encodes
the fraction with numerator $n$ and denominator $m$, whose real value is $n / m$ (taken to be $0$
when $m = 0$).

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Section 2 (fractions `n / m` labelling the trees). -/
noncomputable def natPairToReal (p : ℕ × ℕ) : ℝ :=
  (p.1 : ℝ) / p.2

/-- **Mediant of a gap.** For a gap bounded by two fractions $n_1/m_1$ and $n_2/m_2$, each encoded
as the pair (numerator, denominator) of natural numbers, the mediant is the fraction
$(n_1 + n_2)/(m_1 + m_2)$, encoded as the pair $(n_1 + n_2, m_1 + m_2)$.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Definition 1 (mediant construction). -/
def gapMediant (I : (ℕ × ℕ) × (ℕ × ℕ)) : ℕ × ℕ :=
  (I.1.1 + I.2.1, I.1.2 + I.2.2)

/-- **Children in the Stern–Brocot tree.** Fractions are pairs $(n, m)$ of natural numbers
(numerator, denominator), and the mediant of $a = n_1/m_1$ and $b = n_2/m_2$ is
$a \oplus b = (n_1 + n_2)/(m_1 + m_2)$. The child of a gap $(a, b)$ in direction $L$ is the
gap $(a, a \oplus b)$, and its child in direction $R$ is the gap $(a \oplus b, b)$. For the gap
of a Stern–Brocot vertex, whose label is $a \oplus b$, these are the gaps of its left and right
children.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Definition 1. -/
def sternBrocotChild (I : (ℕ × ℕ) × (ℕ × ℕ)) : SternBrocotLetter → (ℕ × ℕ) × (ℕ × ℕ)
  | .L => (I.1, gapMediant I)
  | .R => (gapMediant I, I.2)

/-- **The Stern–Brocot choice at a vertex.** Let $\alpha$ be a real number and let $(a, b)$ be
a gap with fractions $a = n_1/m_1$ and $b = n_2/m_2$ (pairs of natural numbers). The letter
chosen at $(a, b)$ is $L$ if $\alpha$ is less than the real number $(n_1 + n_2)/(m_1 + m_2)$,
the value of the mediant of $a$ and $b$ (the label of the Stern–Brocot vertex with this gap),
and $R$ otherwise.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Definition 2. -/
noncomputable def sternBrocotChoose (α : ℝ) (I : (ℕ × ℕ) × (ℕ × ℕ)) : SternBrocotLetter :=
  if α < natPairToReal (gapMediant I) then .L else .R

/-- **Gaps along the Stern–Brocot path.** Fractions are pairs (numerator, denominator) of
natural numbers, and the mediant $a \oplus b$ of $a = n_1/m_1$ and $b = n_2/m_2$ is
$(n_1 + n_2)/(m_1 + m_2)$. For a real number $\alpha$, the gaps $I_0(\alpha), I_1(\alpha), \dots$
are defined by $I_0(\alpha) = (0/1, 1/1)$ and, if $I_j(\alpha) = (a, b)$, by
$I_{j+1}(\alpha) = (a, a \oplus b)$ when $\alpha < a \oplus b$ (as real numbers) and
$I_{j+1}(\alpha) = (a \oplus b, b)$ otherwise. The gap $I_j(\alpha)$ is that of the Stern–Brocot
vertex visited at step $j + 1$, whose label is the fraction $f_{j+1}(\alpha)$.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Definition 2. -/
noncomputable def sternBrocotInterval (α : ℝ) : ℕ → (ℕ × ℕ) × (ℕ × ℕ)
  | 0 => ((0, 1), (1, 1))
  | i + 1 => sternBrocotChild (sternBrocotInterval α i)
      (sternBrocotChoose α (sternBrocotInterval α i))

/-- **Stern–Brocot representation.** For a real number $\alpha$, the Stern–Brocot representation
$SB(\alpha) = SB_1(\alpha) SB_2(\alpha) \cdots$ is the infinite sequence over $\{L, R\}$ obtained
by walking down the Stern–Brocot tree from its vertex $1/2$, the vertex with gap $(0/1, 1/1)$.
The vertex with gap $(a, b)$ has label the mediant $a \oplus b$ and children with gaps
$(a, a \oplus b)$ (left) and $(a \oplus b, b)$ (right). If $f_j(\alpha)$ is the label of the
$j$-th vertex of the walk, then $SB_j(\alpha) = L$ and the walk moves to the left child when
$\alpha < f_j(\alpha)$; otherwise $SB_j(\alpha) = R$ and the walk moves to the right child.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Definition 2. -/
noncomputable def sternBrocotRep (α : ℝ) (j : ℕ) : SternBrocotLetter :=
  sternBrocotChoose α (sternBrocotInterval α j)

/-- **Transition rule of the parity sequence.** The map $\mathrm{step}$ sends a letter of the
parity alphabet $\{O_L, E_R, O_R, E_L\}$ and a letter of $\{L, R\}$ to a letter of the parity
alphabet, by $\mathrm{step}(O_L, L) = O_L$, $\mathrm{step}(O_L, R) = E_R$,
$\mathrm{step}(E_R, L) = O_R$, $\mathrm{step}(E_R, R) = O_L$, $\mathrm{step}(O_R, L) = E_L$,
$\mathrm{step}(O_R, R) = O_R$, $\mathrm{step}(E_L, L) = O_R$ and $\mathrm{step}(E_L, R) = O_L$.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Section 3 (definition of `Q`, Figure 5). -/
def mallowsQStep : MallowsParityLetter → SternBrocotLetter → MallowsParityLetter
  | .OL, .L => .OL
  | .OL, .R => .ER
  | .ER, .L => .OR
  | .ER, .R => .OL
  | .OR, .L => .EL
  | .OR, .R => .OR
  | .EL, .L => .OR
  | .EL, .R => .OL

/-- **The parity sequence of a Stern–Brocot word.** Let $x = x_0 x_1 x_2 \cdots$ be an infinite
word over $\{L, R\}$. Its parity sequence $Q(x) = Q_0 Q_1 Q_2 \cdots$ over the parity alphabet
$\{O_L, E_R, O_R, E_L\}$ is defined by $Q_0 = O_L$ and $Q_{j+1} = \mathrm{step}(Q_j, x_j)$ for
every $j \ge 0$, where $\mathrm{step}$ is the transition rule of the parity sequence.

Indices start at $0$ here; the source numbers from $1$, so $Q_0$ is the source's $Q_1(x)$.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Section 3. -/
def mallowsQ (x : ℕ → SternBrocotLetter) : ℕ → MallowsParityLetter
  | 0 => .OL
  | i + 1 => mallowsQStep (mallowsQ x i) (x i)

/-- **Odd positions of a parity sequence.** Let $x = x_0 x_1 x_2 \cdots$ be an infinite sequence
over the parity alphabet $\{O_L, E_R, O_R, E_L\}$, and call a position $j \ge 0$ odd when
$x_j \in \{O_L, O_R\}$. For $i \ge 0$, the $i$-th odd position of $x$ is the $(i+1)$-st smallest
odd position of $x$, and it is $0$ by convention when $x$ has at most $i$ odd positions.

In the source, positions are numbered from $1$ and the odd positions are enumerated as
$o(1) < o(2) < \cdots$; the $i$-th odd position here is $o(i+1) - 1$.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Section 3. -/
noncomputable def mallowsOddIndex (x : ℕ → MallowsParityLetter) : ℕ → ℕ :=
  Nat.nth fun j => x j = .OL ∨ x j = .OR

/-- **The letter rule of $T$.** For a truth value $b$ and letters $a, a'$ of
$\{O_L, E_R, O_R, E_L\}$, the letter $\tau(b, a, a') \in \{L, M, R\}$ is defined as follows. If
$b$ is true, it is $L$ when $a = O_L$ and $R$ otherwise. If $b$ is false, it is $M$ when
$a \ne a'$, $L$ when $a = a' = O_R$, and $R$ when $a = a' \ne O_R$.

If $o(1) < o(2) < \cdots$ are the positions of the letters $O_L$ and $O_R$ in a sequence $x$,
then $T_i(x) = \tau(b, x_{o(i)}, x_{o(i+1)})$, where $b$ is true exactly when
$o(i + 1) = o(i) + 1$.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Section 3 (definition of `T_i`). -/
def mallowsTLetter (adj : Bool) (a b : MallowsParityLetter) : MallowsLetter :=
  if adj then (if a = .OL then .L else .R)
  else if a = b then (if a = .OR then .L else .R) else .M

/-- **The map $T$.** Let $x = \langle x_1, x_2, \dots \rangle$ be a sequence over
$\{O_L, E_R, O_R, E_L\}$ and let $o(1) < o(2) < \cdots$ be the positions $j$ with
$x_j \in \{O_L, O_R\}$. The sequence $T(x) = \langle T_1(x), T_2(x), \dots \rangle$ over
$\{L, M, R\}$ is defined as follows. If $o(i + 1) = o(i) + 1$, then $T_i(x)$ is $L$ when
$x_{o(i)} = O_L$ and $R$ otherwise. If $o(i + 1) \ne o(i) + 1$, then $T_i(x)$ is $M$ when
$x_{o(i)} \ne x_{o(i + 1)}$, $L$ when $x_{o(i)} = x_{o(i + 1)} = O_R$, and $R$ when
$x_{o(i)} = x_{o(i + 1)} \ne O_R$.

If there are only finitely many such positions, $o(i)$ is taken to be $1$ for every $i$ larger
than their number.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Section 3. -/
noncomputable def mallowsT (x : ℕ → MallowsParityLetter) (i : ℕ) : MallowsLetter :=
  mallowsTLetter (decide (mallowsOddIndex x (i + 1) = mallowsOddIndex x i + 1))
    (x (mallowsOddIndex x i)) (x (mallowsOddIndex x (i + 1)))

end

private theorem mallowsRunLetter_ne_next (k : ℕ) :
    (if Even k then MallowsParityLetter.OL else .OR) ≠
      (if Even (k + 1) then MallowsParityLetter.OL else .OR) := by
  by_cases hk : Even k <;> simp [Nat.even_add_one, ← Nat.not_even_iff_odd, hk]

private theorem mallowsT_eq_M_iff_oddLetters_ne (x : ℕ → SternBrocotLetter)
    (hinf : (Set.ofPred fun j => mallowsQ x j = .OL ∨ mallowsQ x j = .OR).Infinite) (i : ℕ) :
    mallowsT (mallowsQ x) i = .M ↔
      mallowsQ x (mallowsOddIndex (mallowsQ x) i) ≠
        mallowsQ x (mallowsOddIndex (mallowsQ x) (i + 1)) := by
  let a := mallowsOddIndex (mallowsQ x) i
  let b := mallowsOddIndex (mallowsQ x) (i + 1)
  have ha : mallowsQ x a = .OL ∨ mallowsQ x a = .OR := Nat.nth_mem_of_infinite hinf i
  have hb : mallowsQ x b = .OL ∨ mallowsQ x b = .OR := Nat.nth_mem_of_infinite hinf (i + 1)
  -- An adjacent odd letter can only repeat the current odd letter.
  have same_of_adj (h : b = a + 1) : mallowsQ x a = mallowsQ x b := by
    rw [h, mallowsQ] at hb ⊢
    rcases ha with ha | ha <;> rw [ha] at hb ⊢ <;> cases hx : x a <;> simp_all [mallowsQStep]
  change mallowsTLetter (decide (b = a + 1)) (mallowsQ x a) (mallowsQ x b) = .M ↔
    mallowsQ x a ≠ mallowsQ x b
  by_cases h : b = a + 1
  · have hab := same_of_adj h
    simp only [h, decide_true, mallowsTLetter, ite_true, hab, ne_self_iff_false, iff_false]
    split <;> simp
  · simp only [h, decide_false, mallowsTLetter, Bool.false_eq_true, ite_false]
    split_ifs <;> simp_all

-- The prescribed runs suffice; keep both named domain hypotheses from the source.
set_option linter.unusedVariables false in
/-- **The letter $M$ in $T(Q(\mathrm{SB}(\alpha)))$ marks the ends of runs.** Let
$\alpha \in (0, 1)$ be irrational, let $x = Q(\mathrm{SB}(\alpha))$ be the sequence over
$\{O_L, E_R, O_R, E_L\}$ obtained from the Stern–Brocot representation $\mathrm{SB}(\alpha)$, and
let $o(1) < o(2) < \cdots$ be the positions $j$ with $x_j \in \{O_L, O_R\}$. Let
$e_1, e_2, \ldots$ be positive integers such that
$(x_{o(1)}, x_{o(2)}, \ldots) = O_L^{e_1} O_R^{e_2} O_L^{e_3} \cdots$, that is, for every
$k \ge 0$ and every $i$ with $e_1 + \cdots + e_k < i \le e_1 + \cdots + e_{k+1}$ (the empty sum
being $0$), $x_{o(i)}$ is $O_L$ if $k$ is even and $O_R$ if $k$ is odd. Then for every $i \ge 1$,
the $i$-th letter $T_i(x)$ of $T(x)$ is $M$ if and only if $i = e_1 + \cdots + e_k$ for some
$k \ge 1$.

The source assumes that $O_L$ and $O_R$ both occur infinitely often among the $x_{o(i)}$; this
is exactly what makes such $e_k$ exist, so the run decomposition is taken as a hypothesis.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Lemma 4 (`integers-2025-A78-lem-4`). -/
public theorem mallowsT_eq_M_iff_runEnd (α : ℝ) (hα : α ∈ Set.Ioo 0 1) (hirr : Irrational α)
    (e : ℕ → ℕ) (he : ∀ k, 0 < e k)
    (hrun : ∀ k i, ∑ t ∈ Finset.range k, e t ≤ i → i < ∑ t ∈ Finset.range (k + 1), e t →
      mallowsQ (sternBrocotRep α) (mallowsOddIndex (mallowsQ (sternBrocotRep α)) i) =
        if Even k then .OL else .OR)
    (i : ℕ) :
    mallowsT (mallowsQ (sternBrocotRep α)) i = .M ↔
      ∃ k, 1 ≤ k ∧ i + 1 = ∑ t ∈ Finset.range k, e t := by
  let x := sternBrocotRep α
  let s (k : ℕ) := ∑ t ∈ Finset.range k, e t
  let oddLetter (j : ℕ) := mallowsQ x (mallowsOddIndex (mallowsQ x) j)
  have hs_step (k : ℕ) : s k < s (k + 1) := by
    dsimp [s]
    rw [Finset.sum_range_succ]
    exact Nat.lt_add_of_pos_right (he k)
  change (∀ k j, s k ≤ j → j < s (k + 1) → oddLetter j = if Even k then .OL else .OR) at hrun
  have hstart (k : ℕ) : oddLetter (s k) = if Even k then .OL else .OR :=
    hrun k (s k) le_rfl (hs_step k)
  have hs_ge (k : ℕ) : k ≤ s k := by
    induction k with
    | zero => exact Nat.zero_le _
    | succ k ih => exact Nat.succ_le_of_lt (ih.trans_lt (hs_step k))
  -- If the odd positions were finite, the indices at both late run starts would default to 0.
  have hinf : (Set.ofPred fun j => mallowsQ x j = .OL ∨ mallowsQ x j = .OR).Infinite := by
    intro hfin
    let k := hfin.toFinset.card
    have hzero₀ : mallowsOddIndex (mallowsQ x) (s k) = 0 := Nat.nth_of_card_le hfin (hs_ge k)
    have hzero₁ : mallowsOddIndex (mallowsQ x) (s (k + 1)) = 0 :=
      Nat.nth_of_card_le hfin ((hs_ge k).trans (hs_step k).le)
    have heq : oddLetter (s k) = oddLetter (s (k + 1)) := by
      dsimp [oddLetter]
      rw [hzero₀, hzero₁]
    exact mallowsRunLetter_ne_next k ((hstart k).symm.trans (heq.trans (hstart (k + 1))))
  have hcover (j : ℕ) : ∃ k, s k ≤ j ∧ j < s (k + 1) := by
    induction j with
    | zero => exact ⟨0, by simp [s], by simpa [s] using he 0⟩
    | succ j ih =>
        obtain ⟨k, hlo, hhi⟩ := ih
        by_cases h : j + 1 < s (k + 1)
        · exact ⟨k, by omega, h⟩
        · exact ⟨k + 1, by omega, (show j + 1 ≤ s (k + 1) by omega).trans_lt (hs_step _)⟩
  rw [mallowsT_eq_M_iff_oddLetters_ne x hinf]
  change oddLetter i ≠ oddLetter (i + 1) ↔ ∃ k, 1 ≤ k ∧ i + 1 = s k
  constructor
  · intro h
    obtain ⟨k, hlo, hhi⟩ := hcover i
    refine ⟨k + 1, by omega, ?_⟩
    by_contra hn
    exact h ((hrun k i hlo hhi).trans (hrun k (i + 1) (by omega) (by omega)).symm)
  · rintro ⟨k, hk, hj⟩
    cases k with
    | zero => omega
    | succ k =>
        have hlo : s k ≤ i := by have := hs_step k; omega
        have hhi : i < s (k + 1) := by omega
        have hnext : i + 1 < s (k + 2) := hj.symm ▸ hs_step (k + 1)
        have h₀ : oddLetter i = _ := hrun k i hlo hhi
        have h₁ : oddLetter (i + 1) = _ := hrun (k + 1) (i + 1) hj.ge hnext
        rw [h₀, h₁]
        exact mallowsRunLetter_ne_next k

end MetaMathlibExt
