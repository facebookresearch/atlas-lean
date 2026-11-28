/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Sort
public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-!
# Permutation Wordle

The theorem `avg_card_correct_second_guess_derangements` gives the average number of correct
positions in the second guess against a derangement. The game and its strategies follow
Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer
Sequences 29 (2026), Article 26.1.7 (arXiv:2506.23452).

The first guess for a secret permutation `π` of `Fin n` is the identity. After each guess the
incorrect positions `I` are revealed, the correct positions are locked, and the next guess
permutes the entries on `I` by the strategy component `S |I|`. With
`I = {i₀ < i₁ < ⋯ < i_{m-1}}`, the entry at `i_j` moves to `i_{S m j}`. Positions are zero-based,
so the paper's one-line component `[2, 3, …, m, 1]` (cyclic shift) is `finRotate m`, and the
paper's guess `γ_{r+1}` is `permWordleGuess S π r`.

## References

* Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
  (2026), Article 26.1.7, pp. 1–16, Sections 2 and 4, Proposition 4 and Theorem 10. The
  ordered-subset restriction formalizes the reduction in the proof of Theorem 10.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Permuting the entries of a map along a set of positions.** Let $I$ be a subset of
$\{0, \dots, n-1\}$ with $k$ elements, listed in increasing order as
$i_0 < i_1 < \dots < i_{k-1}$, let $\sigma$ be a permutation of $\{0, \dots, k-1\}$, and let $g$
be a map from $\{0, \dots, n-1\}$ to itself. Applying $\sigma$ to $g$ along $I$ gives the map that
takes the value $g(i_j)$ at $i_{\sigma(j)}$ for every $j < k$ and agrees with $g$ outside $I$.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Section 2 (the action of a strategy component on `𝓘_r`). -/
def permuteAlong {n k : ℕ} (I : Finset (Fin n)) (h : I.card = k) (σ : Equiv.Perm (Fin k))
    (g : Fin n → Fin n) : Fin n → Fin n :=
  fun i => if hi : i ∈ I then g (I.orderIsoOfFin h (σ.symm ((I.orderIsoOfFin h).symm ⟨i, hi⟩))).1
    else g i

/-- **Permuting along all positions.** Let $\sigma$ be a permutation of $\{0, \dots, n-1\}$ and
let $g$ be a map from $\{0, \dots, n-1\}$ to itself. Applying $\sigma$ to the entries of $g$
along the set of all positions $\{0, \dots, n-1\}$, listed in increasing order, gives the map
$g \circ \sigma^{-1}$.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, proof of Proposition 4 (`γ₂ = S[n]⁻¹`). -/
theorem permuteAlong_univ {n : ℕ} (h : (Finset.univ : Finset (Fin n)).card = n)
    (σ : Equiv.Perm (Fin n)) (g : Fin n → Fin n) :
    permuteAlong Finset.univ h σ g = g ∘ σ.symm := by
  have he : ∀ k, ((Finset.univ : Finset (Fin n)).orderIsoOfFin h k).1 = k := fun k =>
    (congrFun (Finset.orderEmbOfFin_unique (s := (Finset.univ : Finset (Fin n))) h
      (f := id) (fun x => Finset.mem_univ _) strictMono_id) k).symm
  funext i
  have hs : ((Finset.univ : Finset (Fin n)).orderIsoOfFin h).symm ⟨i, Finset.mem_univ i⟩ = i := by
    apply ((Finset.univ : Finset (Fin n)).orderIsoOfFin h).injective
    ext; simp [he]
  simp [permuteAlong, hs, he]

/-- **One round of permutation Wordle.** Let $S$ be a strategy, that is, a permutation $S_m$ of
$\{0, \dots, m-1\}$ for every $m$, let $\pi$ be a permutation of $\{0, \dots, n-1\}$ (the
secret), and let $g$ be a map from $\{0, \dots, n-1\}$ to itself (the current guess). Let $I$ be
the set of incorrect positions, the $k$ with $g(k) \ne \pi(k)$, and let $m$ be the number of
elements of $I$. The next guess agrees with $g$ at every position outside $I$ and permutes the
entries of $g$ on $I$ by $S_m$: writing $I = \{i_0 < i_1 < \dots < i_{m-1}\}$, it takes the value
$g(i_j)$ at $i_{S_m(j)}$ for every $j < m$.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Section 2. -/
def permWordleNextGuess {n : ℕ} (S : (m : ℕ) → Equiv.Perm (Fin m)) (π : Equiv.Perm (Fin n))
    (g : Fin n → Fin n) : Fin n → Fin n :=
  permuteAlong (Finset.univ.filter fun k => g k ≠ π k) rfl (S _) g

/-- **Correct positions stay locked.** Let $S$ be a strategy, that is, a permutation $S_m$ of
$\{0, \dots, m-1\}$ for every $m$, let $\pi$ be a permutation of $\{0, \dots, n-1\}$, and let
$g$ be a map from $\{0, \dots, n-1\}$ to itself. If $g(i) = \pi(i)$ at a position $i$, then the
guess that one round of permutation Wordle with strategy $S$ and secret $\pi$ produces from $g$
also takes the value $g(i)$ at $i$.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Section 2. -/
theorem permWordleNextGuess_of_eq {n : ℕ} (S : (m : ℕ) → Equiv.Perm (Fin m))
    (π : Equiv.Perm (Fin n)) (g : Fin n → Fin n) (i : Fin n) (h : g i = π i) :
    permWordleNextGuess S π g i = g i := by
  simp [permWordleNextGuess, permuteAlong, h]

/-- **One round on the ordered incorrect positions.** Let $S$ be a permutation Wordle strategy,
$\pi$ a secret permutation of $\{0,\ldots,n-1\}$, and $g$ a current guess. If an increasing map $e$
from $\{0,\ldots,m-1\}$ enumerates exactly the positions where $g$ disagrees with $\pi$, then the
next guess has value $g(e(S[m]^{-1}(j)))$ at position $e(j)$ for every $0\le j<m$. -/
theorem permWordleNextGuess_apply_orderEmbedding {m n : ℕ}
    (S : (k : ℕ) → Equiv.Perm (Fin k)) (π : Equiv.Perm (Fin n)) (g : Fin n → Fin n)
    (e : Fin m ↪o Fin n) (he : ∀ i, i ∈ Set.range e ↔ g i ≠ π i) (j : Fin m) :
    permWordleNextGuess S π g (e j) = g (e ((S m).symm j)) := by
  let I := Finset.univ.filter fun i => g i ≠ π i
  have hm : Finset.univ.map e.toEmbedding = I := by
    ext i
    simpa [I, Finset.mem_map, Set.mem_range] using he i
  have hc : I.card = m := by rw [← hm, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  have hE := Finset.orderEmbOfFin_unique hc
    (fun i => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (he _).mp ⟨i, rfl⟩⟩) e.strictMono
  have atRank (k : ℕ) (hk : I.card = k) (i : Fin k) :
      permWordleNextGuess S π g (I.orderEmbOfFin hk i) =
        g (I.orderEmbOfFin hk ((S k).symm i)) := by
    subst k
    have hi := I.orderEmbOfFin_mem rfl i
    have hsub : (⟨I.orderEmbOfFin rfl i, hi⟩ : I) = I.orderIsoOfFin rfl i := by
      apply Subtype.ext
      exact (I.coe_orderIsoOfFin_apply rfl i).symm
    change permuteAlong I rfl (S I.card) g (I.orderEmbOfFin rfl i) = _
    simp only [permuteAlong, dite_eq_left hi, hsub, OrderIso.symm_apply_apply,
      Finset.coe_orderIsoOfFin_apply]
  simpa only [hE] using atRank m hc j

/-- **Guesses of permutation Wordle.** Let $S$ be a strategy, that is, a permutation $S_m$ of
$\{0, \dots, m-1\}$ for every $m$, and let $\pi$ be a permutation of $\{0, \dots, n-1\}$. The
guesses $\gamma_1, \gamma_2, \dots$ of permutation Wordle with strategy $S$ and secret $\pi$ are
the maps from $\{0, \dots, n-1\}$ to itself defined recursively: $\gamma_1$ is the identity, and
$\gamma_{r+1}$ is the guess that one round of the game with strategy $S$ and secret $\pi$
produces from $\gamma_r$. The sequence is indexed from $0$: its term at index $r$ is
$\gamma_{r+1}$.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Section 2. -/
def permWordleGuess {n : ℕ} (S : (m : ℕ) → Equiv.Perm (Fin m)) (π : Equiv.Perm (Fin n)) :
    ℕ → Fin n → Fin n
  | 0 => id
  | r + 1 => permWordleNextGuess S π (permWordleGuess S π r)

/-- **Recurrence for the guesses of permutation Wordle.** Let $S$ be a strategy, that is, a
permutation $S_m$ of $\{0, \dots, m-1\}$ for every $m$, let $\pi$ be a permutation of
$\{0, \dots, n-1\}$, and let $\gamma_1, \gamma_2, \dots$ be the guesses of permutation Wordle with
strategy $S$ and secret $\pi$. For every $r \ge 1$, the guess $\gamma_{r+1}$ is the guess that one
round of the game with strategy $S$ and secret $\pi$ produces from $\gamma_r$.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Section 2. -/
theorem permWordleGuess_succ {n : ℕ} (S : (m : ℕ) → Equiv.Perm (Fin m))
    (π : Equiv.Perm (Fin n)) (r : ℕ) :
    permWordleGuess S π (r + 1) = permWordleNextGuess S π (permWordleGuess S π r) :=
  rfl

/-- **The second guess against a derangement.** Let $S$ be a strategy for permutation Wordle,
that is, a permutation $S_m$ of $\{0, \dots, m-1\}$ for every $m$, and let $\pi$ be a permutation
of $\{0, \dots, n-1\}$ with no fixed point. Then the second guess $\gamma_2$ of permutation Wordle
with strategy $S$ and secret $\pi$ is the inverse permutation $S_n^{-1}$.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, proof of Proposition 4. -/
theorem permWordleGuess_one_of_forall_ne {n : ℕ} (S : (m : ℕ) → Equiv.Perm (Fin m))
    (π : Equiv.Perm (Fin n)) (hπ : ∀ k, π k ≠ k) :
    permWordleGuess S π 1 = ⇑(S n).symm := by
  have key : ∀ (I : Finset (Fin n)) (hI : I = Finset.univ),
      permuteAlong I rfl (S I.card) id = ⇑(S n).symm := by
    intro I hI
    subst hI
    have hc : (Finset.univ : Finset (Fin n)).card = n := by simp
    have gen : ∀ (k : ℕ) (hk : (Finset.univ : Finset (Fin n)).card = k) (hkn : k = n),
        permuteAlong Finset.univ hk (S k) id = ⇑(S n).symm := by
      intro k hk hkn
      subst hkn
      rw [permuteAlong_univ]; rfl
    exact gen _ rfl hc
  exact key _ (Finset.eq_univ_of_forall fun k =>
    Finset.mem_filter.2 ⟨Finset.mem_univ _, (hπ k).symm⟩)

/-- **Permutation Wordle games solved in a given number of guesses.** Let $S$ be a strategy, that
is, a permutation $S_m$ of $\{0, \dots, m-1\}$ for every $m$, let $\pi$ be a permutation of
$\{0, \dots, n-1\}$, and let $\gamma_1, \gamma_2, \dots$ be the guesses of permutation Wordle with
strategy $S$ and secret $\pi$. For a natural number $r$, the game ends after exactly $r$ guesses
when $r \ge 1$, $\gamma_r = \pi$, and $\gamma_j \ne \pi$ for every $j$ with $1 \le j < r$.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Section 4. -/
def PermWordleSolvedIn {n : ℕ} (S : (m : ℕ) → Equiv.Perm (Fin m)) (π : Equiv.Perm (Fin n))
    (r : ℕ) : Prop :=
  1 ≤ r ∧ permWordleGuess S π (r - 1) = ⇑π ∧ ∀ j < r - 1, permWordleGuess S π j ≠ ⇑π

/-- **Games won with the first guess.** Let $S$ be a strategy, that is, a permutation $S_m$ of
$\{0, \dots, m-1\}$ for every $m$, and let $\pi$ be a permutation of $\{0, \dots, n-1\}$. Then
permutation Wordle with strategy $S$ and secret $\pi$ ends after exactly one guess if and only if
$\pi$ is the identity.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, proof of Theorem 5. -/
theorem permWordleSolvedIn_one_iff {n : ℕ} (S : (m : ℕ) → Equiv.Perm (Fin m))
    (π : Equiv.Perm (Fin n)) : PermWordleSolvedIn S π 1 ↔ π = 1 := by
  simp only [PermWordleSolvedIn, le_refl, Nat.sub_self, permWordleGuess, Nat.not_lt_zero,
    IsEmpty.forall_iff, implies_true, and_true, true_and]
  constructor
  · intro h; ext i; simp [← h]
  · rintro rfl; rfl

/-- **An exact solve needs only the last two guesses.** For every permutation Wordle strategy
$S$, every secret permutation $\pi$ of $\{0,\ldots,n-1\}$, and every $r\ge 2$, the game ends in
exactly $r$ guesses if and only if $\gamma_r=\pi$ and $\gamma_{r-1}\ne\pi$, where $\gamma_j$ is
$S$'s $j$-th guess against $\pi$. -/
theorem permWordleSolvedIn_succ_succ_iff {n : ℕ} (S : (m : ℕ) → Equiv.Perm (Fin m))
    (π : Equiv.Perm (Fin n)) (j : ℕ) :
    PermWordleSolvedIn S π (j + 2) ↔
      permWordleGuess S π (j + 1) = ⇑π ∧ permWordleGuess S π j ≠ ⇑π := by
  have lock (k : ℕ) (h : permWordleGuess S π k = ⇑π) :
      permWordleGuess S π (k + 1) = ⇑π := by
    rw [permWordleGuess_succ, h]
    exact funext fun i => permWordleNextGuess_of_eq S π π i rfl
  have persist {k l : ℕ} (hkl : k ≤ l) (h : permWordleGuess S π k = ⇑π) :
      permWordleGuess S π l = ⇑π := by
    induction hkl with
    | refl => exact h
    | step _ ih => exact lock _ ih
  have hj : j + 2 - 1 = j + 1 := by omega
  rw [PermWordleSolvedIn, hj, and_iff_right (by omega : 1 ≤ j + 2)]
  exact and_congr_right fun _ => ⟨fun h => h j (Nat.lt_succ_self j),
    fun h k hk he => h (persist (Nat.le_of_lt_succ hk) he)⟩

private theorem guesses_extendDomain {n : ℕ} (I : Finset (Fin n))
    (S T : (m : ℕ) → Equiv.Perm (Fin m)) (hST : ∀ m ≤ I.card, S m = T m)
    (π : Equiv.Perm (Fin I.card)) :
    let e := I.orderEmbOfFin rfl
    let π' := π.extendDomain (I.orderIsoOfFin rfl).toEquiv
    ∀ r, (∀ i, permWordleGuess S π' r (e i) = e (permWordleGuess T π r i)) ∧
      ∀ i ∉ I, permWordleGuess S π' r i = i := by
  intro e π' r
  have hπ (i : Fin I.card) : π' (e i) = e (π i) := Equiv.Perm.extendDomain_apply_image ..
  have hπout (i : Fin n) (hi : i ∉ I) : π' i = i :=
    Equiv.Perm.extendDomain_apply_not_subtype _ _ hi
  induction r with
  | zero => exact ⟨fun _ => rfl, fun _ _ => rfl⟩
  | succ r ih =>
    let g := permWordleGuess T π r
    let G := permWordleGuess S π' r
    let J := Finset.univ.filter fun i => g i ≠ π i
    let f := J.orderEmbOfFin rfl
    have small (i : Fin I.card) : i ∈ Set.range f ↔ g i ≠ π i := by
      simp [f, J, Finset.range_orderEmbOfFin]
    have related (i : Fin I.card) : G (e i) = e (g i) := ih.1 i
    have large (x : Fin n) : x ∈ Set.range (f.trans e) ↔ G x ≠ π' x := by
      constructor
      · rintro ⟨j, rfl⟩
        change G (e (f j)) ≠ π' (e (f j))
        rw [related, hπ]
        exact e.injective.ne ((small _).mp ⟨j, rfl⟩)
      · intro hx
        have hxI : x ∈ I := by
          by_contra h
          exact hx ((ih.2 x h).trans (hπout x h).symm)
        obtain ⟨i, rfl⟩ : x ∈ Set.range e := (I.range_orderEmbOfFin rfl).symm ▸ hxI
        rw [related, hπ] at hx
        obtain ⟨j, rfl⟩ := (small i).mpr (fun h => hx (congrArg e h))
        exact ⟨j, rfl⟩
    simp only [permWordleGuess_succ]
    refine ⟨fun i => ?_, fun i hi => ?_⟩
    · change permWordleNextGuess S π' G (e i) = e (permWordleNextGuess T π g i)
      by_cases hi : g i = π i
      · have hi' : G (e i) = π' (e i) := (related i).trans ((congrArg e hi).trans (hπ i).symm)
        rw [permWordleNextGuess_of_eq S π' G (e i) hi', permWordleNextGuess_of_eq T π g i hi]
        exact related i
      · obtain ⟨j, rfl⟩ := (small i).mpr hi
        have hc : J.card ≤ I.card := (Finset.card_filter_le _ _).trans_eq (Fintype.card_fin _)
        change permWordleNextGuess S π' G ((f.trans e) j) = e (permWordleNextGuess T π g (f j))
        rw [permWordleNextGuess_apply_orderEmbedding S π' G (f.trans e) large j,
          permWordleNextGuess_apply_orderEmbedding T π g f small j, hST _ hc]
        exact related _
    · exact (permWordleNextGuess_of_eq S π' G i
        ((ih.2 i hi).trans (hπout i hi).symm)).trans (ih.2 i hi)

/-- **Restricting permutation Wordle to an ordered subset preserves the solve time.** Let $I$ be
an $m$-element subset of $\{0,\ldots,n-1\}$ and identify $\{0,\ldots,m-1\}$ with $I$ in increasing
order. Let $S,T$ be strategies with $S[k]=T[k]$ for all $0\le k\le m$. For a permutation $\pi$ of
$\{0,\ldots,m-1\}$, let $\widetilde\pi$ act by $\pi$ on $I$ under this identification and fix every
position outside $I$. For every $r\in\mathbb N$, $S$ solves $\widetilde\pi$ in exactly $r$ guesses
if and only if $T$ solves $\pi$ in exactly $r$ guesses. -/
theorem permWordleSolvedIn_extendDomain_iff {n : ℕ} (I : Finset (Fin n))
    (S T : (m : ℕ) → Equiv.Perm (Fin m)) (hST : ∀ m ≤ I.card, S m = T m)
    (π : Equiv.Perm (Fin I.card)) (r : ℕ) :
    PermWordleSolvedIn S (π.extendDomain (I.orderIsoOfFin rfl).toEquiv) r ↔
      PermWordleSolvedIn T π r := by
  let e := I.orderEmbOfFin rfl
  let π' := π.extendDomain (I.orderIsoOfFin rfl).toEquiv
  have happly (j : ℕ) : permWordleGuess S π' j = ⇑π' ↔ permWordleGuess T π j = ⇑π := by
    obtain ⟨hin, hout⟩ := guesses_extendDomain I S T hST π j
    have hπ (i : Fin I.card) : π' (e i) = e (π i) := Equiv.Perm.extendDomain_apply_image ..
    constructor
    · intro h
      exact funext fun i => e.injective ((hin i).symm.trans ((congrFun h (e i)).trans (hπ i)))
    · intro h
      funext i
      by_cases hi : i ∈ I
      · obtain ⟨j, rfl⟩ : i ∈ Set.range e := (I.range_orderEmbOfFin rfl).symm ▸ hi
        exact (hin j).trans ((congrArg e (congrFun h j)).trans (hπ j).symm)
      · exact (hout i hi).trans (Equiv.Perm.extendDomain_apply_not_subtype _ _ hi).symm
  change PermWordleSolvedIn S π' r ↔ _
  simp only [PermWordleSolvedIn, ne_eq, happly]

/-- **Coefficients of the guess-count generating function.** For a strategy $S$ and natural
numbers $n$ and $r$, the coefficient $[x^r] f_S(x)$ of the generating function of $S$ at length
$n$ is the number of secret permutations of $\{0, \dots, n-1\}$ that $S$ guesses in exactly $r$
guesses.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Section 4. -/
noncomputable def permWordleCoeff (S : (m : ℕ) → Equiv.Perm (Fin m)) (n r : ℕ) : ℕ :=
  Nat.card {π : Equiv.Perm (Fin n) // PermWordleSolvedIn S π r}

/-- **No permutation is guessed in zero guesses.** For every strategy $S$ and every $n$, write
$f_S$ for the generating function whose coefficient $[x^r] f_S$ is the number of permutations of
$\{0, \dots, n-1\}$ that $S$ guesses in exactly $r$ guesses. Then the constant coefficient
$[x^0] f_S$ vanishes.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Section 4. -/
theorem permWordleCoeff_zero (S : (m : ℕ) → Equiv.Perm (Fin m)) (n : ℕ) :
    permWordleCoeff S n 0 = 0 := by
  have : IsEmpty {π : Equiv.Perm (Fin n) // PermWordleSolvedIn S π 0} :=
    ⟨fun π => absurd π.2.1 (by norm_num)⟩
  simp [permWordleCoeff]

/-- **First guess with a correct position in permutation Wordle.** Let $S$ be a strategy, that
is, a permutation $S_m$ of $\{0, \dots, m-1\}$ for every $m$, let $\pi$ be a permutation of
$\{0, \dots, n-1\}$, and let $\gamma_1, \gamma_2, \dots$ be the guesses of permutation Wordle with
strategy $S$ and secret $\pi$. For a natural number $r$, $\rho_S(\pi) = r$ means that $r \ge 1$,
that $\gamma_r(k) = \pi(k)$ for some position $k$, and that for every $j$ with $1 \le j < r$ there
is no position $k$ with $\gamma_j(k) = \pi(k)$.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Section 4.2. -/
def PermWordleFirstCorrectAt {n : ℕ} (S : (m : ℕ) → Equiv.Perm (Fin m))
    (π : Equiv.Perm (Fin n)) (r : ℕ) : Prop :=
  1 ≤ r ∧ (∃ k, permWordleGuess S π (r - 1) k = π k) ∧
    ∀ j < r - 1, ∀ k, permWordleGuess S π j k ≠ π k

/-- **Permutations with a correct entry in the first guess.** For $n \in \mathbb{N}$, a strategy
$S$ and a permutation $\pi$ of $\{0, \dots, n-1\}$, write $\rho_S(\pi) = r$ when the $r$-th guess
is the first guess with a correct position for the secret $\pi$. Then $\rho_S(\pi) = 1$, that is,
the first guess (the identity) already has a correct position, exactly when $\pi$ has a fixed
point.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, proof of Theorem 10. -/
theorem permWordleFirstCorrectAt_one_iff {n : ℕ} (S : (m : ℕ) → Equiv.Perm (Fin m))
    (π : Equiv.Perm (Fin n)) : PermWordleFirstCorrectAt S π 1 ↔ ∃ k, π k = k := by
  simp only [PermWordleFirstCorrectAt, le_refl, Nat.sub_self, permWordleGuess, id,
    Nat.not_lt_zero, IsEmpty.forall_iff, implies_true, and_true, true_and]
  exact ⟨fun ⟨k, hk⟩ => ⟨k, hk.symm⟩, fun ⟨k, hk⟩ => ⟨k, hk.symm⟩⟩

/-- **Cyclic shift strategy.** A strategy assigns to each $m$ a permutation of $m$ positions, used
to rearrange the entries on the $m$ incorrect positions of a guess. The cyclic shift strategy
$\mathrm{CS}$ has component $\mathrm{CS}[m] = [2, 3, \dots, m, 1]$ in one-line notation, that is,
the rotation $i \mapsto i + 1 \pmod m$ of $\{0, 1, \dots, m-1\}$.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Section 2. -/
def cyclicShiftStrategy : (m : ℕ) → Equiv.Perm (Fin m) :=
  fun m => finRotate m

/-- **Components of the cyclic shift strategy.** For every $m$, the component of the cyclic shift
strategy on $m$ positions is the rotation $i \mapsto i + 1 \pmod m$ of $\{0, 1, \dots, m-1\}$.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Section 2. -/
theorem cyclicShiftStrategy_apply (m : ℕ) : cyclicShiftStrategy m = finRotate m :=
  rfl

/-- **Cyclic shift left strategy.** For $n \in \mathbb{N}$, the strategy $\mathrm{CSL}_n$ assigns
to each $m$ a permutation of $m$ positions: for $m = n$ the left cyclic shift
$[m, 1, 2, \dots, m-1]$ in one-line notation, that is, $i \mapsto i - 1 \pmod m$, and for every
$m \ne n$ the right cyclic shift $[2, 3, \dots, m, 1]$, that is, $i \mapsto i + 1 \pmod m$.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Section 4.3. -/
def cyclicShiftLeftStrategy (n : ℕ) : (m : ℕ) → Equiv.Perm (Fin m) :=
  fun m => if m = n then (finRotate m).symm else finRotate m

/-- **Top component of the left-shift strategy.** For every $n$, the component on $n$ positions
of the left-shift strategy $\mathrm{CSL}_n$ is the left cyclic shift $j \mapsto j - 1 \bmod n$
of $\{0, \dots, n-1\}$, the inverse of the cyclic shift $j \mapsto j + 1 \bmod n$.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Section 4.3. -/
theorem cyclicShiftLeftStrategy_self (n : ℕ) :
    cyclicShiftLeftStrategy n n = (finRotate n).symm := by
  simp [cyclicShiftLeftStrategy]

/-- **Non-top components of the left-shift strategy.** For all $n$ and $m$ with $m \ne n$, the
component on $m$ positions of the left-shift strategy $\mathrm{CSL}_n$ is the cyclic shift
$j \mapsto j + 1 \bmod m$ of $\{0, \dots, m-1\}$.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Section 4.3. -/
theorem cyclicShiftLeftStrategy_of_ne {n m : ℕ} (h : m ≠ n) :
    cyclicShiftLeftStrategy n m = finRotate m := by
  simp [cyclicShiftLeftStrategy, h]

/-- **Inductive strategy.** A strategy $S$ (a permutation $S[m]$ of $\{0, \dots, m-1\}$ for each
$m$) is inductive of length $n$ when $S[m]$ is the rotation $i \mapsto i + 1 \pmod m$ for every
$m < n$, and $S[n]$ is an $n$-cycle, that is, a single cycle moving every element of
$\{0, \dots, n-1\}$.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Section 3.1. -/
def IsInductivePermWordleStrategy (n : ℕ) (S : (m : ℕ) → Equiv.Perm (Fin m)) : Prop :=
  (∀ m < n, S m = finRotate m) ∧ (S n).IsCycle ∧ (S n).support = Finset.univ

namespace avg_card_correct_second_guess_derangements

open Finset in
private theorem card_derangements_with_image {n : ℕ} {i j : Fin n} (hj : j ≠ i) :
    let D := univ.filter (fun d : Equiv.Perm (Fin n) => ∀ k, d k ≠ k)
    (n - 1) * (D.filter fun d => d i = j).card = D.card := by
  intro D
  -- Relabeling by a transposition that fixes i exchanges the two fibers.
  have fiber_eq (k : Fin n) (hk : k ≠ i) :
      (D.filter fun d => d i = k).card = (D.filter fun d => d i = j).card := by
    let e := Equiv.swap k j
    have hi : e.symm i = i := Equiv.swap_apply_of_ne_of_ne hk.symm hj.symm
    apply card_equiv e.permCongr
    intro d
    simp only [D, mem_filter, mem_univ, true_and]
    refine and_congr (e.forall_congr fun x => by simp) ?_
    rw [Equiv.permCongr_apply, hi, ← Equiv.swap_apply_left k j]
    exact e.injective.eq_iff.symm
  symm
  calc
    D.card = ∑ k ∈ univ.erase i, (D.filter fun d => d i = k).card :=
      card_eq_sum_card_fiberwise fun d hd =>
        mem_erase.mpr ⟨(mem_filter.mp hd).2 i, mem_univ _⟩
    _ = (univ.erase i).card * (D.filter fun d => d i = j).card :=
      sum_const_nat fun k hk => fiber_eq k (ne_of_mem_erase hk)
    _ = _ := by simp

end avg_card_correct_second_guess_derangements

open avg_card_correct_second_guess_derangements in
/-- **Average number of correct positions in the second guess.** Let $n \ge 2$ and let $S$ be a
permutation Wordle strategy (a permutation $S[m]$ of $\{0, \dots, m-1\}$ for each $m$) whose
component $S[n]$ has no fixed point. For a secret permutation $\pi$ of $\{0, \dots, n-1\}$ let
$\gamma_2$ be the second guess of $S$. The sum, over all derangements $\pi$ of
$\{0, \dots, n-1\}$, of the number of positions $i$ with $\gamma_2(i) = \pi(i)$, divided by the
number of derangements of $\{0, \dots, n-1\}$, equals $n/(n-1)$.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Proposition 4 (`jis-2026-26.1.7-prop-4`). -/
theorem avg_card_correct_second_guess_derangements (n : ℕ) (hn : 2 ≤ n)
    (S : (m : ℕ) → Equiv.Perm (Fin m)) (hS : ∀ k, S n k ≠ k) :
    (∑ d ∈ Finset.univ.filter (fun d : Equiv.Perm (Fin n) => ∀ k, d k ≠ k),
        ((Finset.univ.filter fun i => permWordleGuess S d 1 i = d i).card : ℚ)) /
      (Finset.univ.filter (fun d : Equiv.Perm (Fin n) => ∀ k, d k ≠ k)).card =
      (n : ℚ) / (n - 1) := by
  let D := Finset.univ.filter (fun d : Equiv.Perm (Fin n) => ∀ k, d k ≠ k)
  let σ := (S n).symm
  have hσ (i : Fin n) : σ i ≠ i := fun h => hS i ((S n).symm_apply_eq.mp h).symm
  have hcount :
      (∑ d ∈ D, (Finset.univ.filter fun i => permWordleGuess S d 1 i = d i).card) * (n - 1) =
        n * D.card := by
    have hsum : (∑ d ∈ D, (Finset.univ.filter fun i => permWordleGuess S d 1 i = d i).card) =
        ∑ i, (D.filter fun d => d i = σ i).card := by
      calc
        _ = ∑ d ∈ D, (Finset.univ.filter fun i => d i = σ i).card := by
          apply Finset.sum_congr rfl
          intro d hd
          rw [permWordleGuess_one_of_forall_ne S d (Finset.mem_filter.mp hd).2]
          simp only [σ, eq_comm]
        _ = _ := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
          (fun (d : Equiv.Perm (Fin n)) i => d i = σ i)
    rw [hsum, Finset.sum_mul]
    calc
      _ = (Finset.univ : Finset (Fin n)).card * D.card :=
        Finset.sum_const_nat fun i _ =>
          (Nat.mul_comm ..).trans (card_derangements_with_image (hσ i))
      _ = _ := by simp
  have hD : 0 < D.card :=
    Finset.card_pos.mpr ⟨S n, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS⟩⟩
  have hn' : (1 : ℚ) < n := by exact_mod_cast (show 1 < n by omega)
  apply (div_eq_div_iff (by exact_mod_cast hD.ne') (sub_ne_zero.mpr hn'.ne')).2
  simpa [D, Nat.cast_sub (show 1 ≤ n by omega)] using congrArg (Nat.cast : ℕ → ℚ) hcount

end

end MetaMathlibExt
