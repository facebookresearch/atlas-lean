/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Topology.GDelta.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

import Mathlib.Order.ConditionallyCompletePartialOrder.Indexed
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.LocallyClosed
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# The Banach–Mazur game

Winning strategies for the two players in the interval game on the real line are characterized
by local comeagreness and global meagreness, respectively.
-/

@[expose] public section

namespace MathlibExt.Topology.ScottishBook43Wanted

/-- **Valid strategies in the Banach–Mazur game.** A strategy in the Banach–Mazur game is a map
$\sigma \colon \mathbb{R} \times \mathbb{R} \to \mathbb{R} \times \mathbb{R}$, a pair $(a, b)$
standing for the open interval $(a, b)$. It is valid if for all reals $a < b$ the pair
$(c, d) = \sigma(a, b)$ satisfies $a \le c < d \le b$, so that it answers each nonempty open
interval with a nonempty open subinterval, possibly the interval itself. Nothing is required of
$\sigma$ on pairs $(a, b)$ with $a \ge b$.

Strategies are taken to depend only on the opponent's last move: the rest of the game depends
only on the current interval. -/
def BanachMazurStrategyValid (σ : (ℝ × ℝ) → ℝ × ℝ) : Prop :=
  ∀ I : ℝ × ℝ, I.1 < I.2 → (σ I).1 < (σ I).2 ∧
    Set.Ioo (σ I).1 (σ I).2 ⊆ Set.Ioo I.1 I.2

/-- **Plays of the Banach–Mazur game.** Let $(a, b)$ be a pair of reals and let $\sigma_A$ and
$\sigma_B$ be strategies for A and B, maps from pairs of reals to pairs of reals. A sequence
$(p_n)_{n \ge 0}$ of pairs of reals is the play that opens with $(a, b)$ and follows $\sigma_A$
and $\sigma_B$ if $p_0 = (a, b)$, $p_{n+1} = \sigma_B(p_n)$ for every even $n$, and
$p_{n+1} = \sigma_A(p_n)$ for every odd $n$: A opens at index $0$ and moves at the other even
indices, B moves at the odd indices. -/
def BanachMazurPlayConsistent (first : ℝ × ℝ) (σA σB : (ℝ × ℝ) → ℝ × ℝ)
    (p : ℕ → ℝ × ℝ) : Prop :=
  p 0 = first ∧ ∀ n : ℕ,
    (n % 2 = 0 → p (n + 1) = σB (p n)) ∧ (n % 2 = 1 → p (n + 1) = σA (p n))

/-- **Winning strategy for the first player in the Banach–Mazur game.** Let
$E \subseteq \mathbb{R}$. In this game a move is a pair of reals $(c, d)$, standing for the open
interval $(c, d)$, and a valid strategy is a map from pairs to pairs answering each pair $(c, d)$
with $c < d$ by a pair $(c', d')$ with $c \le c' < d' \le d$. Player A has a winning strategy for
$E$ if there are reals $a < b$ and a valid strategy $\sigma_A$ such that, for every valid strategy
$\sigma_B$, the play $(c_n, d_n)_{n \ge 0}$ given by $(c_0, d_0) = (a, b)$,
$(c_{n+1}, d_{n+1}) = \sigma_B(c_n, d_n)$ for even $n$ and
$(c_{n+1}, d_{n+1}) = \sigma_A(c_n, d_n)$ for odd $n$ satisfies
$\left(\bigcap_{n} (c_n, d_n)\right) \cap E \neq \emptyset$. -/
def BanachMazurAHasWinningStrategy (E : Set ℝ) : Prop :=
  ∃ first : ℝ × ℝ, ∃ σA : (ℝ × ℝ) → ℝ × ℝ, first.1 < first.2 ∧
    BanachMazurStrategyValid σA ∧
    ∀ σB : (ℝ × ℝ) → ℝ × ℝ, BanachMazurStrategyValid σB →
      ∀ p : ℕ → ℝ × ℝ, BanachMazurPlayConsistent first σA σB p →
        (⋂ n, Set.Ioo (p n).1 (p n).2) ∩ E ≠ ∅

/-- **Winning strategy for the second player in the Banach–Mazur game.** Let
$E \subseteq \mathbb{R}$. In this game a move is a pair of reals $(c, d)$, standing for the open
interval $(c, d)$, and a valid strategy is a map from pairs to pairs answering each pair $(c, d)$
with $c < d$ by a pair $(c', d')$ with $c \le c' < d' \le d$. Player B has a winning strategy for
$E$ if there is a valid strategy $\sigma_B$ such that, for all reals $a < b$ and every valid
strategy $\sigma_A$, the play $(c_n, d_n)_{n \ge 0}$ given by $(c_0, d_0) = (a, b)$,
$(c_{n+1}, d_{n+1}) = \sigma_B(c_n, d_n)$ for even $n$ and
$(c_{n+1}, d_{n+1}) = \sigma_A(c_n, d_n)$ for odd $n$ satisfies
$\left(\bigcap_{n} (c_n, d_n)\right) \cap E = \emptyset$. -/
def BanachMazurBHasWinningStrategy (E : Set ℝ) : Prop :=
  ∃ σB : (ℝ × ℝ) → ℝ × ℝ, BanachMazurStrategyValid σB ∧
    ∀ first : ℝ × ℝ, ∀ σA : (ℝ × ℝ) → ℝ × ℝ, first.1 < first.2 →
      BanachMazurStrategyValid σA →
      ∀ p : ℕ → ℝ × ℝ, BanachMazurPlayConsistent first σA σB p →
        (⋂ n, Set.Ioo (p n).1 (p n).2) ∩ E = ∅

open Set Filter TopologicalSpace

private abbrev Move := ℝ × ℝ
private abbrev Strategy := Move → Move
private abbrev interval (I : Move) := Ioo I.1 I.2
private abbrev Legal (I J : Move) := J.1 < J.2 ∧ interval J ⊆ interval I

private lemma even_step {I A B p} (hp : BanachMazurPlayConsistent I A B p) (n : ℕ) :
    p (2 * n + 1) = B (p (2 * n)) :=
  (hp.2 _).1 (by omega)

private lemma odd_step {I A B p} (hp : BanachMazurPlayConsistent I A B p) (n : ℕ) :
    p (2 * (n + 1)) = A (p (2 * n + 1)) := by
  convert (hp.2 (2 * n + 1)).2 (by omega) using 2

private lemma exists_play (I : Move) (A B : Strategy) :
    ∃ p, BanachMazurPlayConsistent I A B p := by
  let p : ℕ → Move := Nat.rec I fun n J => if n % 2 = 0 then B J else A J
  refine ⟨p, rfl, fun n => ⟨fun h => ite_eq_left h, fun h => ite_eq_right (by omega)⟩⟩

private lemma legal_moves {I A B p} (hp : BanachMazurPlayConsistent I A B p)
    (hI : I.1 < I.2) (hA : BanachMazurStrategyValid A) (hB : BanachMazurStrategyValid B) :
    ∀ n, (p n).1 < (p n).2 ∧ interval (p (n + 1)) ⊆ interval (p n) := by
  have step (n : ℕ) (hn : (p n).1 < (p n).2) : Legal (p n) (p (n + 1)) := by
    by_cases h : n % 2 = 0
    · rw [(hp.2 n).1 h]
      exact hB _ hn
    · rw [(hp.2 n).2 (by omega)]
      exact hA _ hn
  have good (n : ℕ) : (p n).1 < (p n).2 := by
    induction n with
    | zero => simpa only [hp.1] using hI
    | succ n ih => exact (step n ih).1
  exact fun n => ⟨good n, (step n (good n)).2⟩

private lemma tail_consistent {I A B p} (hp : BanachMazurPlayConsistent I A B p) :
    BanachMazurPlayConsistent (p 1) B A (fun n => p (n + 1)) :=
  ⟨rfl, fun n => ⟨fun h => (hp.2 _).2 (by omega), fun h => (hp.2 _).1 (by omega)⟩⟩

private lemma tail_inter {p : ℕ → Move} (h : interval (p 1) ⊆ interval (p 0)) :
    (⋂ n, interval (p (n + 1))) = ⋂ n, interval (p n) := by
  ext x
  simp only [mem_iInter]
  exact ⟨fun hx n => by cases n with
    | zero => exact h (hx 0)
    | succ n => exact hx n, fun hx n => hx (n + 1)⟩

-- Choose a response for the first requirement the current interval has yet to meet.
-- This recovers progress through a countable family using only the last move.
private lemma choose_response {I : Move} {U : ℕ → Set ℝ} {P : Move → Prop}
    (h : ∀ n, ∃ J, P J ∧ interval J ⊆ interval I ∧ interval J ⊆ U n) :
    ∃ J, P J ∧ interval J ⊆ interval I ∧
      ∀ n, (∀ k < n, interval I ⊆ U k) → interval J ⊆ U n := by
  classical
  by_cases hex : ∃ n, ¬ interval I ⊆ U n
  · obtain ⟨J, hJ, hsub, hU⟩ := h (Nat.find hex)
    refine ⟨J, hJ, hsub, fun n hn => ?_⟩
    by_cases hle : n < Nat.find hex
    · exact hsub.trans (not_not.mp (Nat.find_min hex hle))
    · have heq : n = Nat.find hex := by
        by_contra! hne
        exact Nat.find_spec hex (hn _ (by omega))
      exact heq ▸ hU
  · push Not at hex
    obtain ⟨J, hJ, hsub, _⟩ := h 0
    exact ⟨J, hJ, hsub, fun n _ => hsub.trans (hex n)⟩

-- After n full rounds the first n requirements hold throughout the current interval.
private lemma inter_subset_requirements {p : ℕ → Move} {U : ℕ → Set ℝ}
    (step : ∀ i n, (∀ k < n, interval (p (2 * i)) ⊆ U k) →
      interval (p (2 * (i + 1))) ⊆ U n) :
    (⋂ n, interval (p n)) ⊆ ⋂ n, U n := by
  have progress (i : ℕ) : ∀ k < i, interval (p (2 * i)) ⊆ U k := by
    induction i with
    | zero => omega
    | succ i ih => exact fun k hk => step i k fun j hj => ih j (by omega)
  exact fun x hx => mem_iInter.2 fun n =>
    progress (n + 1) n (by omega) (mem_iInter.1 hx _)

-- A response whose closed interval lies inside the input prevents the intersection
-- of the nested open intervals from losing its limit at an endpoint.
private lemma force_residual {S : Set ℝ} (hS : S ∈ residual ℝ) :
    ∃ B, BanachMazurStrategyValid B ∧ ∀ I A p, I.1 < I.2 → BanachMazurStrategyValid A →
      BanachMazurPlayConsistent I A B p →
      (⋂ n, interval (p n)).Nonempty ∧ (⋂ n, interval (p n)) ⊆ S := by
  classical
  obtain ⟨G, hGS, hG, hd⟩ := mem_residual.1 hS
  obtain ⟨U, hU, rfl⟩ := hG.eq_iInter_nat
  have chooseMove (I : Move) : ∃ J, I.1 < I.2 →
      (J.1 < J.2 ∧ Icc J.1 J.2 ⊆ interval I) ∧ interval J ⊆ interval I ∧
        ∀ n, (∀ k < n, interval I ⊆ U k) → interval J ⊆ U n := by
    by_cases hI : I.1 < I.2
    · apply Exists.imp (fun _ hh _ => hh)
      apply choose_response
      intro n
      have hdU := hd.mono (iInter_subset U n)
      obtain ⟨a, b, hab, hsub⟩ := (isOpen_Ioo.inter (hU n)).exists_Ioo_subset
        (hdU.inter_open_nonempty (interval I) isOpen_Ioo (nonempty_Ioo.2 hI))
      obtain ⟨c, hac, hcb⟩ := exists_between hab
      obtain ⟨d, hcd, hdb⟩ := exists_between hcb
      have hclosed : Icc c d ⊆ Ioo a b := fun _ hx => ⟨hac.trans_le hx.1, hx.2.trans_lt hdb⟩
      have hboth := hclosed.trans hsub
      exact ⟨(c, d), ⟨hcd, hboth.trans inter_subset_left⟩,
        Ioo_subset_Icc_self.trans (hboth.trans inter_subset_left),
        Ioo_subset_Icc_self.trans (hboth.trans inter_subset_right)⟩
    · exact ⟨I, fun h => (hI h).elim⟩
  choose B hB using chooseMove
  have valid : BanachMazurStrategyValid B := fun I hI => ⟨(hB I hI).1.1, (hB I hI).2.1⟩
  refine ⟨B, valid, fun I A p hI hA hp => ?_⟩
  have moves := legal_moves hp hI hA valid
  have nested : Antitone (fun n => interval (p n)) := antitone_nat_of_succ_le fun n => (moves n).2
  have endpoints (n : ℕ) := (Ioo_subset_Ioo_iff (moves (n + 1)).1).1 (moves n).2
  have left : Monotone (fun n => (p n).1) := monotone_nat_of_le_succ fun n => (endpoints n).1
  have right : Antitone (fun n => (p n).2) := antitone_nat_of_succ_le fun n => (endpoints n).2
  have hx := left.ciSup_mem_iInter_Icc_of_antitone right (fun n => (moves n).1.le)
  constructor
  · refine ⟨⨆ n, (p n).1, mem_iInter.2 fun n => nested (show n ≤ 2 * n by omega) ?_⟩
    apply (hB _ (moves (2 * n)).1).1.2
    rw [← even_step hp]
    exact mem_iInter.1 hx _
  · refine (inter_subset_requirements (U := U) ?_).trans hGS
    intro i n hn
    have hsub := (hB _ (moves (2 * i)).1).2.2 n hn
    rw [← even_step hp] at hsub
    exact (nested (show 2 * i + 1 ≤ 2 * (i + 1) by omega)).trans hsub

-- Within each basic open set V the union of all possible responses is open and dense in V.
-- Off its frontier, a point of V therefore belongs to an actual response.
private lemma reachable_residual {A : Strategy} (hA : BanachMazurStrategyValid A) :
    ∀ᶠ x in residual ℝ, ∀ V : Set ℝ, IsOpen V → x ∈ V →
      ∃ J : Move, J.1 < J.2 ∧ interval J ⊆ V ∧ x ∈ interval (A J) := by
  let responses (V : Set ℝ) :=
    ⋃ (J : Move) (_ : J.1 < J.2) (_ : interval J ⊆ V), interval (A J)
  have ho V : IsOpen (responses V) :=
    isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_Ioo
  have hcl V (hV : IsOpen V) : V ⊆ closure (responses V) := by
    intro x hx
    apply mem_closure_iff.2
    intro W hW hxW
    obtain ⟨a, b, hab, hsub⟩ := (hW.inter hV).exists_Ioo_subset ⟨x, hxW, hx⟩
    let J : Move := (a, b)
    obtain ⟨y, hy⟩ := nonempty_Ioo.2 (hA J hab).1
    refine ⟨y, (hsub ((hA J hab).2 hy)).1, ?_⟩
    exact mem_iUnion.2 ⟨J, mem_iUnion.2 ⟨hab, mem_iUnion.2 ⟨hsub.trans inter_subset_right, hy⟩⟩⟩
  have hres : ∀ᶠ x in residual ℝ, ∀ V ∈ countableBasis ℝ, x ∈ coborder (responses V) := by
    apply (eventually_countable_ball (countable_countableBasis ℝ)).2
    intro V _
    exact residual_of_dense_open (ho V).isLocallyClosed.isOpen_coborder dense_coborder
  filter_upwards [hres] with x hx
  intro V hV hxV
  obtain ⟨W, hW, hxW, hWV⟩ := (isBasis_countableBasis ℝ).exists_subset_of_mem_open hxV hV
  have hm := mem_coborder_iff_imp.1 (hx W hW) (hcl W (isOpen_of_mem_countableBasis hW) hxW)
  change x ∈ ⋃ (J : Move) (_ : J.1 < J.2) (_ : interval J ⊆ W), interval (A J) at hm
  simp only [mem_iUnion, exists_prop] at hm
  obtain ⟨J, hJ, hsub, hxJ⟩ := hm
  exact ⟨J, hJ, hsub.trans hWV, hxJ⟩

-- At each reachable point x, the opponent can keep x in play and force the
-- intersection into every basic ball about x, hence make it exactly {x}.
private lemma singleton_counterplay {A : Strategy} (hA : BanachMazurStrategyValid A) :
    ∀ᶠ x in residual ℝ, ∃ B, BanachMazurStrategyValid B ∧ ∀ I, x ∈ interval I →
      ∀ p, BanachMazurPlayConsistent I A B p → (⋂ n, interval (p n)) = {x} := by
  classical
  filter_upwards [reachable_residual hA] with x hx
  let U (n : ℕ) := Metric.ball x (1 / (n + 1 : ℝ))
  have chooseMove (I : Move) : ∃ J, (I.1 < I.2 → Legal I J) ∧
      (x ∈ interval I → x ∈ interval (A J) ∧
        ∀ n, (∀ k < n, interval I ⊆ U k) → interval J ⊆ U n) := by
    by_cases hxI : x ∈ interval I
    · have chosen : ∃ J, (J.1 < J.2 ∧ x ∈ interval (A J)) ∧ interval J ⊆ interval I ∧
          ∀ n, (∀ k < n, interval I ⊆ U k) → interval J ⊆ U n := by
        apply choose_response
        intro n
        obtain ⟨J, hJ, hsub, hresp⟩ := hx (interval I ∩ U n) (isOpen_Ioo.inter Metric.isOpen_ball)
          ⟨hxI, Metric.mem_ball_self (by positivity)⟩
        exact ⟨J, ⟨hJ, hresp⟩, hsub.trans inter_subset_left, hsub.trans inter_subset_right⟩
      obtain ⟨J, ⟨hJ, hxJ⟩, hsub, hstep⟩ := chosen
      exact ⟨J, fun _ => ⟨hJ, hsub⟩, fun _ => ⟨hxJ, hstep⟩⟩
    · exact ⟨I, fun hi => ⟨hi, Subset.rfl⟩, fun hi => (hxI hi).elim⟩
  choose B hB using chooseMove
  have valid : BanachMazurStrategyValid B := fun I => (hB I).1
  refine ⟨B, valid, fun I hxI p hp => ?_⟩
  have moves := legal_moves hp (hxI.1.trans hxI.2) hA valid
  have hxEven (i : ℕ) : x ∈ interval (p (2 * i)) := by
    induction i with
    | zero => simpa only [Nat.mul_zero, hp.1] using hxI
    | succ i ih =>
      rw [odd_step hp, even_step hp]
      exact ((hB _).2 ih).1
  have nested : Antitone (fun n => interval (p n)) := antitone_nat_of_succ_le fun n => (moves n).2
  apply Subset.antisymm
  · have hsub : (⋂ n, interval (p n)) ⊆ ⋂ n, U n := by
      apply inter_subset_requirements
      intro i n hn
      have h := ((hB _).2 (hxEven i)).2 n hn
      rw [← even_step hp] at h
      exact (nested (show 2 * i + 1 ≤ 2 * (i + 1) by omega)).trans h
    intro y hy
    change y = x
    by_contra hne
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (dist_pos.mpr hne)
    exact (Metric.mem_ball.1 (mem_iInter.1 (hsub hy) n)).not_gt hn
  · exact singleton_subset_iff.2 (mem_iInter.2 fun n => nested (by omega : n ≤ 2 * n) (hxEven n))

/--
**Banach–Mazur game theorem.** For every set $E \subseteq \mathbb{R}$, player A has a winning
strategy in the Banach–Mazur game for $E$ if and only if there are reals $a < b$ such that
$(a, b) \setminus E$ is meagre, and player B has a winning strategy in the Banach–Mazur game for
$E$ if and only if $E$ is meagre.

This answers Mazur's Problem 43 of the Scottish Book. Given $E$, A picks an interval $d_1$,
B picks a subinterval $d_2$ of $d_1$, A picks a subinterval $d_3$ of $d_2$, and so on; A wins if
the intersection of all the chosen intervals meets $E$. Mazur asked whether A has a winning
method only when the complement of $E$ is of first category in some interval, and whether B has
one when $E$ is of first category. Both answers are affirmative, in the characterization form
above (Oxtoby).

Source: S. Mazur, Problem 43 of the Scottish Book; addendum of S. Banach,
4 August 1935: "Mazur's conjecture is true"; J. C. Oxtoby, The Banach-Mazur
game and Banach category theorem; see the commentary in R. D. Mauldin (ed.),
The Scottish Book, 2nd ed. (Birkhäuser, 2015).
-/
theorem banach_mazur_winning_strategy_characterization :
    ∀ E : Set ℝ,
      (BanachMazurAHasWinningStrategy E ↔
        ∃ a b : ℝ, a < b ∧ IsMeagre (Set.Ioo a b \ E)) ∧
      (BanachMazurBHasWinningStrategy E ↔ IsMeagre E) := by
  intro E
  constructor
  · constructor
    · rintro ⟨I, A, hI, hA, win⟩
      refine ⟨I.1, I.2, hI, ?_⟩
      change ∀ᶠ x in residual ℝ, x ∉ interval I \ E
      filter_upwards [singleton_counterplay hA] with x hx
      rintro ⟨hxI, hxE⟩
      obtain ⟨B, hB, hplay⟩ := hx
      obtain ⟨p, hp⟩ := exists_play I A B
      have hwin := nonempty_iff_ne_empty.2 (win B hB p hp)
      rw [hplay I hxI p hp] at hwin
      exact hxE (singleton_inter_nonempty.1 hwin)
    · rintro ⟨a, b, hab, hm⟩
      obtain ⟨A, hA, force⟩ := force_residual hm
      refine ⟨(a, b), A, hab, hA, fun B hB p hp => ?_⟩
      have moves := legal_moves hp hab hA hB
      have ht := force _ B _ (moves 1).1 hB (tail_consistent hp)
      rw [tail_inter (moves 0).2] at ht
      obtain ⟨x, hx⟩ := ht.1
      have hxI := mem_iInter.1 hx 0
      rw [hp.1] at hxI
      exact nonempty_iff_ne_empty.1 ⟨x, hx, by
        by_contra hxE
        exact ht.2 hx ⟨hxI, hxE⟩⟩
  · constructor
    · rintro ⟨B, hB, win⟩
      change ∀ᶠ x in residual ℝ, x ∉ E
      filter_upwards [singleton_counterplay hB] with x hx
      obtain ⟨A, hA, hplay⟩ := hx
      let I : Move := (x - 1, x + 1)
      have hxI : x ∈ interval I := ⟨sub_one_lt _, lt_add_one _⟩
      obtain ⟨p, hp⟩ := exists_play I B A
      have moves := legal_moves hp (hxI.1.trans hxI.2) hB hA
      have he := win (p 1) A (moves 1).1 hA _ (tail_consistent hp)
      change (⋂ n, interval (p (n + 1))) ∩ E = ∅ at he
      rw [tail_inter (moves 0).2, hplay I hxI p hp] at he
      exact singleton_inter_eq_empty.1 he
    · intro hm
      obtain ⟨B, hB, force⟩ := force_residual hm
      refine ⟨B, hB, fun I A hI hA p hp => ?_⟩
      exact eq_empty_iff_forall_notMem.2 fun x hx => (force I A p hI hA hp).2 hx.1 hx.2

end MathlibExt.Topology.ScottishBook43Wanted
