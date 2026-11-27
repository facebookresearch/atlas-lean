/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.QuantumGates.GateAction
public import CSLibExt.Computability.Complexity.QMA.ThresholdOperator

/-!
# A threshold counter circuit

A unary one-hot counter on `k` input qubits at arbitrary injective
positions `L`: an X gate places the marker in work cell `0` (and removes it at the end);
processing input `i` shifts the marker one cell up, through `i + 1` Fredkin gates controlled
on that input (each Fredkin is CNOT, Toffoli, CNOT); the target qubit is
then flipped once from every work cell at or above the threshold `T`;
finally the computation is uncomputed. On states supported on clean work
ancillas the circuit is exactly the basis permutation that flips the
target iff at least `T` inputs are set, with `k + 1` work qubits and at
most `8 (k + 1)^2` gates. The counter construction is not from the cited source, which covers only
the Fredkin decomposition; its contract is the four theorems below (well-formedness, size, exact
basis action, and the bridge to `QMA.acceptCount`).

Source: M. A. Nielsen and I. L. Chuang, Quantum Computation and Quantum
Information, Cambridge University Press, 2000, Chapter 4 (Fredkin gate
from Toffoli and CNOT).
-/

@[expose] public section

namespace Cslib.Complexity.Classes.QuantumGates

set_option autoImplicit false

/-- Work ancillas used by the threshold counter on `k` inputs. -/
def thresholdWork (k : ℕ) : ℕ := k + 1

/-- Position of input `i` (`0` when `i ≥ k`). -/
def thresholdInputPos (k : ℕ) (L : Fin (k + 1 + thresholdWork k) → ℕ) (i : ℕ) : ℕ :=
  if h : i < k then L (Fin.castAdd (thresholdWork k) (Fin.castSucc ⟨i, h⟩)) else 0

/-- Position of the target qubit. -/
def thresholdTargetPos (k : ℕ) (L : Fin (k + 1 + thresholdWork k) → ℕ) : ℕ :=
  L (Fin.castAdd (thresholdWork k) (Fin.last k))

/-- Position of work cell `j` (`0` when `j ≥ k + 1`). -/
def thresholdWorkPos (k : ℕ) (L : Fin (k + 1 + thresholdWork k) → ℕ) (j : ℕ) : ℕ :=
  if h : j < thresholdWork k then L (Fin.natAdd (k + 1) ⟨j, h⟩) else 0

/-- Fredkin gate (swap `x` and `y` when `c` is set): CNOT, Toffoli, CNOT. -/
def fredkinGates (c x y : ℕ) : List QGate :=
  controlledGate xGate y x :: (toffoliGates c x y ++ [controlledGate xGate y x])

/-- Fredkin triples `(c, cell j, cell (j + 1))` for `j = n - 1, …, 0` (descending). -/
def thresholdSwapTriples (k : ℕ) (L : Fin (k + 1 + thresholdWork k) → ℕ) (c n : ℕ) :
    List (ℕ × ℕ × ℕ) :=
  (List.range n).reverse.map fun j => (c, thresholdWorkPos k L j, thresholdWorkPos k L (j + 1))

/-- All compute triples: input `i` swaps cell pairs `(j, j + 1)` for `j = i` down to `0`,
controlled on input `i`, moving the marker up one cell when the input is set. -/
def thresholdComputeTriples (k : ℕ) (L : Fin (k + 1 + thresholdWork k) → ℕ) :
    List (ℕ × ℕ × ℕ) :=
  (List.range k).flatMap fun i => thresholdSwapTriples k L (thresholdInputPos k L i) (i + 1)

/-- The gates of one Fredkin triple. -/
def thresholdTripleGates (p : ℕ × ℕ × ℕ) : List QGate :=
  fredkinGates p.1 p.2.1 p.2.2

/-- Work cells at or above the threshold. -/
def thresholdFlipCells (k T : ℕ) : List ℕ :=
  (List.range (thresholdWork k)).filter fun j => decide (T ≤ j)

/-- One CNOT from each work cell at or above the threshold to the target. -/
def thresholdFlipGates (k T : ℕ) (L : Fin (k + 1 + thresholdWork k) → ℕ) : List QGate :=
  (thresholdFlipCells k T).flatMap fun j =>
    [controlledGate xGate (thresholdWorkPos k L j) (thresholdTargetPos k L)]

/-- X on work cell `0` (target as spectator): places and removes the marker. -/
def thresholdMarkerGate (k : ℕ) (L : Fin (k + 1 + thresholdWork k) → ℕ) : QGate :=
  embeddedGate xGate (thresholdWorkPos k L 0) (thresholdTargetPos k L)

/-- Threshold-`T` counter gates under layout `L`: inputs at
`L (Fin.castAdd _ (Fin.castSucc i))`, target at
`L (Fin.castAdd _ (Fin.last k))`, work cells at
`L (Fin.natAdd (k + 1) j)`. Unary one-hot construction (compute,
threshold, uncompute); the theorems below are its contract. -/
def thresholdCounterGates (k T : ℕ) (L : Fin (k + 1 + thresholdWork k) → ℕ) :
    List QGate :=
  thresholdMarkerGate k L ::
    ((thresholdComputeTriples k L).flatMap thresholdTripleGates ++
      (thresholdFlipGates k T L ++
        ((thresholdComputeTriples k L).reverse.flatMap thresholdTripleGates ++
          [thresholdMarkerGate k L])))

/-- Number of input qubits set in basis index `t`. -/
def thresholdInputCount {N : ℕ} (k : ℕ) (L : Fin (k + 1 + thresholdWork k) → ℕ)
    (t : Fin (2 ^ N)) : ℕ :=
  (Finset.univ.filter fun i : Fin k =>
    qBit (L (Fin.castAdd (thresholdWork k) (Fin.castSucc i))) t.val = 1).card

/-- The basis permutation: flip the target bit iff at least `T` inputs are set (an involution,
hence a permutation, when the target is not an input position, e.g. for injective `L`). -/
def thresholdCounterFlip (N k T : ℕ) (L : Fin (k + 1 + thresholdWork k) → ℕ)
    (t : Fin (2 ^ N)) : Fin (2 ^ N) :=
  if T ≤ thresholdInputCount k L t then
    flipBit N (L (Fin.castAdd (thresholdWork k) (Fin.last k))) t
  else t

/-- Basis pullback of `fredkinGates c x y`. -/
private def fredkinIndex (N c x y : ℕ) (s : Fin (2 ^ N)) : Fin (2 ^ N) :=
  cnotIndex N y x (toffoliIndex N c x y (cnotIndex N y x s))

private def tripleIndex (N : ℕ) (p : ℕ × ℕ × ℕ) (s : Fin (2 ^ N)) : Fin (2 ^ N) :=
  fredkinIndex N p.1 p.2.1 p.2.2 s

/-- Triples applied first-to-last. -/
private def tripleFwd (N : ℕ) (tr : List (ℕ × ℕ × ℕ)) (s : Fin (2 ^ N)) : Fin (2 ^ N) :=
  tr.foldl (fun s p => tripleIndex N p s) s

/-- Pullback of `tr.flatMap thresholdTripleGates` (last triple first). -/
private def tripleBwd (N : ℕ) (tr : List (ℕ × ℕ × ℕ)) (s : Fin (2 ^ N)) : Fin (2 ^ N) :=
  tr.foldr (tripleIndex N) s

private def thresholdFlipIndex (N k T : ℕ) (L : Fin (k + 1 + thresholdWork k) → ℕ)
    (s : Fin (2 ^ N)) : Fin (2 ^ N) :=
  (thresholdFlipCells k T).foldr
    (fun j s => cnotIndex N (thresholdWorkPos k L j) (thresholdTargetPos k L) s) s

/-- The whole circuit's basis pullback. -/
private def thresholdSigma (N k T : ℕ) (L : Fin (k + 1 + thresholdWork k) → ℕ)
    (t : Fin (2 ^ N)) : Fin (2 ^ N) :=
  flipBit N (thresholdWorkPos k L 0)
    (tripleBwd N (thresholdComputeTriples k L)
      (thresholdFlipIndex N k T L
        (tripleFwd N (thresholdComputeTriples k L) (flipBit N (thresholdWorkPos k L 0) t))))

/-- Work cells hold exactly the marker at cell `p`. -/
private def thresholdOneHot (N k : ℕ) (L : Fin (k + 1 + thresholdWork k) → ℕ) (p : ℕ)
    (s : Fin (2 ^ N)) : Prop :=
  ∀ j, j < thresholdWork k → qBit (thresholdWorkPos k L j) s.val = if j = p then 1 else 0

/-- `s'` agrees with `s` off the work cells. -/
private def thresholdOffWorkEq (N k : ℕ) (L : Fin (k + 1 + thresholdWork k) → ℕ)
    (s s' : Fin (2 ^ N)) : Prop :=
  ∀ r, (∀ j, j < thresholdWork k → r ≠ thresholdWorkPos k L j) → qBit r s'.val = qBit r s.val

/-- All work cells clear (the negation of `hψ`'s premise). -/
private def thresholdClean (N k : ℕ) (L : Fin (k + 1 + thresholdWork k) → ℕ)
    (s : Fin (2 ^ N)) : Prop :=
  ∀ j : Fin (thresholdWork k), qBit (L (Fin.natAdd (k + 1) j)) s.val = 0

/-- Set inputs among the first `m`. -/
private def thresholdPrefixCount (N k : ℕ) (L : Fin (k + 1 + thresholdWork k) → ℕ) (m : ℕ)
    (s : Fin (2 ^ N)) : ℕ :=
  (Finset.univ.filter fun i : Fin k =>
    i.val < m ∧ qBit (thresholdInputPos k L i.val) s.val = 1).card
/-- In-range work position unfolds to the layout entry. -/
private theorem thresholdWorkPos_of_lt {k : ℕ} (L : Fin (k + 1 + thresholdWork k) → ℕ)
    {j : ℕ} (hj : j < thresholdWork k) :
    thresholdWorkPos k L j = L (Fin.natAdd (k + 1) ⟨j, hj⟩) := by
  simp [thresholdWorkPos, hj]

/-- In-range input position unfolds to the layout entry. -/
private theorem thresholdInputPos_of_lt {k : ℕ} (L : Fin (k + 1 + thresholdWork k) → ℕ)
    {i : ℕ} (hi : i < k) :
    thresholdInputPos k L i = L (Fin.castAdd (thresholdWork k) (Fin.castSucc ⟨i, hi⟩)) := by
  simp [thresholdInputPos, hi]

/-- In-range work positions are in range. -/
private theorem thresholdWorkPos_lt {N k : ℕ} {L : Fin (k + 1 + thresholdWork k) → ℕ}
    (hLN : ∀ i, L i < N) {j : ℕ} (hj : j < thresholdWork k) :
    thresholdWorkPos k L j < N := by
  rw [thresholdWorkPos_of_lt L hj]
  exact hLN _

/-- In-range input positions are in range. -/
private theorem thresholdInputPos_lt {N k : ℕ} {L : Fin (k + 1 + thresholdWork k) → ℕ}
    (hLN : ∀ i, L i < N) {i : ℕ} (hi : i < k) :
    thresholdInputPos k L i < N := by
  rw [thresholdInputPos_of_lt L hi]
  exact hLN _

/-- The target position is in range. -/
private theorem thresholdTargetPos_lt {N k : ℕ} {L : Fin (k + 1 + thresholdWork k) → ℕ}
    (hLN : ∀ i, L i < N) :
    thresholdTargetPos k L < N := by
  unfold thresholdTargetPos
  exact hLN _

/-- Work positions are injective in the cell index. -/
private theorem thresholdWorkPos_inj {N k : ℕ} {L : Fin (k + 1 + thresholdWork k) → ℕ}
    (hL : Function.Injective L) {j j' : ℕ} (hj : j < thresholdWork k)
    (hj' : j' < thresholdWork k)
    (h : thresholdWorkPos k L j = thresholdWorkPos k L j') : j = j' := by
  rw [thresholdWorkPos_of_lt L hj, thresholdWorkPos_of_lt L hj'] at h
  have hval := congrArg Fin.val (hL h)
  simp only [Fin.val_natAdd] at hval
  omega

/-- Work positions avoid input positions. -/
private theorem thresholdWorkPos_ne_inputPos {N k : ℕ}
    {L : Fin (k + 1 + thresholdWork k) → ℕ} (hL : Function.Injective L)
    {j i : ℕ} (hj : j < thresholdWork k) (hi : i < k) :
    thresholdWorkPos k L j ≠ thresholdInputPos k L i := by
  intro hcon
  rw [thresholdWorkPos_of_lt L hj, thresholdInputPos_of_lt L hi] at hcon
  have hval := congrArg Fin.val (hL hcon)
  simp only [Fin.val_natAdd, Fin.val_castAdd, Fin.val_castSucc] at hval
  simp only [thresholdWork] at hj
  omega

/-- Work positions avoid the target. -/
private theorem thresholdWorkPos_ne_targetPos {N k : ℕ}
    {L : Fin (k + 1 + thresholdWork k) → ℕ} (hL : Function.Injective L)
    {j : ℕ} (hj : j < thresholdWork k) :
    thresholdWorkPos k L j ≠ thresholdTargetPos k L := by
  intro hcon
  rw [thresholdWorkPos_of_lt L hj] at hcon
  unfold thresholdTargetPos at hcon
  have hval := congrArg Fin.val (hL hcon)
  simp only [Fin.val_natAdd, Fin.val_castAdd, Fin.val_last] at hval
  simp only [thresholdWork] at hj
  omega

/-- Input positions avoid the target. -/
private theorem thresholdInputPos_ne_targetPos {N k : ℕ}
    {L : Fin (k + 1 + thresholdWork k) → ℕ} (hL : Function.Injective L)
    {i : ℕ} (hi : i < k) :
    thresholdInputPos k L i ≠ thresholdTargetPos k L := by
  intro hcon
  rw [thresholdInputPos_of_lt L hi] at hcon
  unfold thresholdTargetPos at hcon
  have hval := congrArg Fin.val (hL hcon)
  simp only [Fin.val_castAdd, Fin.val_castSucc, Fin.val_last] at hval
  omega

/-- A flatMap of pullback blocks pulls back by the foldr of their index maps. -/
private theorem applyCircuit_flatMap_pullback {α : Type*} {N : ℕ}
    (l : List α) (gs : α → List QGate) (idx : α → Fin (2 ^ N) → Fin (2 ^ N))
    (h : ∀ a ∈ l, ∀ (φ : Fin (2 ^ N) → ℂ) (s : Fin (2 ^ N)),
      applyCircuit N (gs a) φ s = φ (idx a s))
    (ψ : Fin (2 ^ N) → ℂ) (s : Fin (2 ^ N)) :
    applyCircuit N (l.flatMap gs) ψ s = ψ (l.foldr idx s) := by
  revert h ψ s
  induction l with
  | nil =>
    intro h ψ s
    rfl
  | cons a as ih =>
    intro h ψ s
    simp only [List.flatMap_cons, List.foldr_cons]
    rw [applyCircuit_append]
    have h_head : ∀ (φ : Fin (2 ^ N) → ℂ) (t : Fin (2 ^ N)),
        applyCircuit N (gs a) φ t = φ (idx a t) :=
      fun φ t => h a List.mem_cons_self φ t
    have h_tail : ∀ b ∈ as, ∀ (φ : Fin (2 ^ N) → ℂ) (t : Fin (2 ^ N)),
        applyCircuit N (gs b) φ t = φ (idx b t) :=
      fun b hb φ t => h b (List.mem_cons_of_mem a hb) φ t
    rw [ih h_tail (applyCircuit N (gs a) ψ) s]
    exact h_head ψ (as.foldr idx s)

/-- A foldr of self-inverses undoes the matching foldl. -/
private theorem foldr_foldl_cancel {α β : Type*} (f : α → β → β) (l : List α)
    (hf : ∀ a ∈ l, ∀ b, f a (f a b) = b) (b : β) :
    l.foldr f (l.foldl (fun b a => f a b) b) = b := by
  induction l generalizing b with
  | nil => simp
  | cons a l ih =>
    have htail : ∀ a' ∈ l, ∀ c, f a' (f a' c) = c :=
      fun a' ha' c => hf a' (List.mem_cons_of_mem _ ha') c
    simp only [List.foldl_cons, List.foldr_cons]
    rw [ih htail _]
    exact hf a List.mem_cons_self b

/-- A foldl of self-inverses undoes the matching foldr. -/
private theorem foldl_foldr_cancel {α β : Type*} (f : α → β → β) (l : List α)
    (hf : ∀ a ∈ l, ∀ b, f a (f a b) = b) (b : β) :
    l.foldl (fun b a => f a b) (l.foldr f b) = b := by
  induction l generalizing b with
  | nil => simp
  | cons a l ih =>
    have htail : ∀ a' ∈ l, ∀ c, f a' (f a' c) = c :=
      fun a' ha' c => hf a' (List.mem_cons_of_mem _ ha') c
    simp only [List.foldl_cons, List.foldr_cons]
    rw [hf a List.mem_cons_self _]
    exact ih htail _

/-- A foldr commutes with a function commuting with every step. -/
private theorem foldr_comm_of_comm {α β : Type*} (f : α → β → β) (g : β → β)
    (l : List α) (hfg : ∀ a ∈ l, ∀ b, f a (g b) = g (f a b)) (b : β) :
    l.foldr f (g b) = g (l.foldr f b) := by
  induction l generalizing b with
  | nil => rfl
  | cons a l ih =>
    simp only [List.foldr]
    rw [ih (fun a' ha' => hfg a' (by simp [ha']))]
    exact hfg a (by simp) _

/-- A foldr of injective steps is injective. -/
private theorem foldr_injective {α β : Type*} (f : α → β → β) (l : List α)
    (hf : ∀ a ∈ l, Function.Injective (f a)) :
    Function.Injective (fun b => l.foldr f b) := by
  induction l with
  | nil =>
    intro b1 b2 h
    simpa [List.foldr] using h
  | cons a l ih =>
    have ha : Function.Injective (f a) := hf a (by simp)
    have htail : ∀ a' ∈ l, Function.Injective (f a') :=
      fun a' ha' => hf a' (by simp [ha'])
    have ih' := ih htail
    simp only [List.foldr]
    exact ha.comp ih'

/-- Length of a flatMap with constant block length. -/
private theorem length_flatMap_const {α β : Type*} (l : List α) (f : α → List β)
    (c : ℕ) (hf : ∀ a, (f a).length = c) :
    (l.flatMap f).length = c * l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp [List.flatMap_cons, List.length_append, hf a, ih]
      ring

/-- Closed form of the Fredkin pullback: swap bits `x`, `y` iff the
control is set and the two bits differ. -/
private theorem fredkinIndex_eq {N c x y : ℕ} (hcx : c ≠ x) (_hcy : c ≠ y)
    (hxy : x ≠ y) (hxN : x < N) (hyN : y < N) (s : Fin (2 ^ N)) :
    fredkinIndex N c x y s =
      if qBit c s.val = 1 ∧ qBit x s.val ≠ qBit y s.val then
        flipBit N x (flipBit N y s)
      else s := by

  have hyx : y ≠ x := fun h => hxy h.symm
  have hfin0 : ∀ a : Fin 2, a ≠ 1 → a = 0 := by decide
  by_cases hc : qBit c s.val = 1
  · by_cases hx : qBit x s.val = 1
    · by_cases hy : qBit y s.val = 1
      · -- 1,1,1 => s
        have heq : qBit x s.val = qBit y s.val := by rw [hx, hy]
        have hexp : ¬ (qBit c s.val = 1 ∧ qBit x s.val ≠ qBit y s.val) :=
          fun h => h.2 heq
        unfold fredkinIndex cnotIndex toffoliIndex
        rw [ite_eq_left hy]
        have hx_s1 : qBit x (flipBit N x s).val = 0 := by
          rw [qBit_flipBit_self hxN s, hx]; decide
        have hx1 : ¬ qBit x (flipBit N x s).val = 1 := by rw [hx_s1]; decide
        have htoff : ¬ (qBit c (flipBit N x s).val = 1 ∧ qBit x (flipBit N x s).val = 1) :=
          fun h => hx1 h.2
        rw [ite_eq_right htoff]
        have hy_s1 : qBit y (flipBit N x s).val = 1 := by
          rw [qBit_flipBit_of_ne hyx s]; exact hy
        rw [ite_eq_left hy_s1]
        rw [ite_eq_right hexp]
        exact flipBit_flipBit N x s
      · -- 1,1,0 => double
        have hy0 : qBit y s.val = 0 := hfin0 _ hy
        have hne : qBit x s.val ≠ qBit y s.val := by rw [hx, hy0]; decide
        have hexp : qBit c s.val = 1 ∧ qBit x s.val ≠ qBit y s.val := ⟨hc, hne⟩
        unfold fredkinIndex cnotIndex toffoliIndex
        rw [ite_eq_right hy]
        have htoff : qBit c s.val = 1 ∧ qBit x s.val = 1 := ⟨hc, hx⟩
        rw [ite_eq_left htoff]
        have hy_flip : qBit y (flipBit N y s).val = 1 := by
          rw [qBit_flipBit_self hyN s, hy0]; decide
        rw [ite_eq_left hy_flip]
        rw [ite_eq_left hexp]
    · by_cases hy : qBit y s.val = 1
      · -- 1,0,1 => double (comm)
        have hx0 : qBit x s.val = 0 := hfin0 _ hx
        have hne : qBit x s.val ≠ qBit y s.val := by rw [hx0, hy]; decide
        have hexp : qBit c s.val = 1 ∧ qBit x s.val ≠ qBit y s.val := ⟨hc, hne⟩
        unfold fredkinIndex cnotIndex toffoliIndex
        rw [ite_eq_left hy]
        have hc_s1 : qBit c (flipBit N x s).val = 1 := by
          rw [qBit_flipBit_of_ne hcx s]; exact hc
        have hx_s1 : qBit x (flipBit N x s).val = 1 := by
          rw [qBit_flipBit_self hxN s, hx0]; decide
        have htoff : qBit c (flipBit N x s).val = 1 ∧ qBit x (flipBit N x s).val = 1 :=
          ⟨hc_s1, hx_s1⟩
        rw [ite_eq_left htoff]
        have hy_s1 : qBit y (flipBit N x s).val = 1 := by
          rw [qBit_flipBit_of_ne hyx s]; exact hy
        have hy_s2 : qBit y (flipBit N y (flipBit N x s)).val = 0 := by
          rw [qBit_flipBit_self hyN (flipBit N x s), hy_s1]; decide
        have hy_final : ¬ qBit y (flipBit N y (flipBit N x s)).val = 1 := by
          rw [hy_s2]; decide
        rw [ite_eq_right hy_final]
        rw [ite_eq_left hexp]
        exact flipBit_comm N y x s
      · -- 1,0,0 => s
        have hx0 : qBit x s.val = 0 := hfin0 _ hx
        have hy0 : qBit y s.val = 0 := hfin0 _ hy
        have heq : qBit x s.val = qBit y s.val := by rw [hx0, hy0]
        have hexp : ¬ (qBit c s.val = 1 ∧ qBit x s.val ≠ qBit y s.val) :=
          fun h => h.2 heq
        unfold fredkinIndex cnotIndex toffoliIndex
        rw [ite_eq_right hy]
        have htoff : ¬ (qBit c s.val = 1 ∧ qBit x s.val = 1) := fun h => hx h.2
        rw [ite_eq_right htoff]
        rw [ite_eq_right hy]
        rw [ite_eq_right hexp]
  · by_cases hx : qBit x s.val = 1
    · by_cases hy : qBit y s.val = 1
      · -- 0,1,1 => s
        have hexp : ¬ (qBit c s.val = 1 ∧ qBit x s.val ≠ qBit y s.val) :=
          fun h => hc h.1
        unfold fredkinIndex cnotIndex toffoliIndex
        rw [ite_eq_left hy]
        have hc_flip : qBit c (flipBit N x s).val = qBit c s.val :=
          qBit_flipBit_of_ne hcx s
        have hc1 : ¬ qBit c (flipBit N x s).val = 1 := by rw [hc_flip]; exact hc
        have htoff : ¬ (qBit c (flipBit N x s).val = 1 ∧ qBit x (flipBit N x s).val = 1) :=
          fun h => hc1 h.1
        rw [ite_eq_right htoff]
        have hy_flip : qBit y (flipBit N x s).val = 1 := by
          rw [qBit_flipBit_of_ne hyx s]; exact hy
        rw [ite_eq_left hy_flip]
        rw [ite_eq_right hexp]
        exact flipBit_flipBit N x s
      · -- 0,1,0 => s
        have hexp : ¬ (qBit c s.val = 1 ∧ qBit x s.val ≠ qBit y s.val) :=
          fun h => hc h.1
        unfold fredkinIndex cnotIndex toffoliIndex
        rw [ite_eq_right hy]
        have htoff : ¬ (qBit c s.val = 1 ∧ qBit x s.val = 1) := fun h => hc h.1
        rw [ite_eq_right htoff]
        rw [ite_eq_right hy]
        rw [ite_eq_right hexp]
    · by_cases hy : qBit y s.val = 1
      · -- 0,0,1 => s
        have hexp : ¬ (qBit c s.val = 1 ∧ qBit x s.val ≠ qBit y s.val) :=
          fun h => hc h.1
        unfold fredkinIndex cnotIndex toffoliIndex
        rw [ite_eq_left hy]
        have hc_flip : qBit c (flipBit N x s).val = qBit c s.val :=
          qBit_flipBit_of_ne hcx s
        have hc1 : ¬ qBit c (flipBit N x s).val = 1 := by rw [hc_flip]; exact hc
        have htoff : ¬ (qBit c (flipBit N x s).val = 1 ∧ qBit x (flipBit N x s).val = 1) :=
          fun h => hc1 h.1
        rw [ite_eq_right htoff]
        have hy_flip : qBit y (flipBit N x s).val = 1 := by
          rw [qBit_flipBit_of_ne hyx s]; exact hy
        rw [ite_eq_left hy_flip]
        rw [ite_eq_right hexp]
        exact flipBit_flipBit N x s
      · -- 0,0,0 => s
        have hexp : ¬ (qBit c s.val = 1 ∧ qBit x s.val ≠ qBit y s.val) :=
          fun h => hc h.1
        unfold fredkinIndex cnotIndex toffoliIndex
        rw [ite_eq_right hy]
        have htoff : ¬ (qBit c s.val = 1 ∧ qBit x s.val = 1) := fun h => hc h.1
        rw [ite_eq_right htoff]
        rw [ite_eq_right hy]
        rw [ite_eq_right hexp]

/-- The Fredkin pullback is an involution on distinct in-range qubits. -/
private theorem fredkinIndex_involutive {N c x y : ℕ} (hcx : c ≠ x) (hcy : c ≠ y)
    (hxy : x ≠ y) (hxN : x < N) (hyN : y < N) (s : Fin (2 ^ N)) :
    fredkinIndex N c x y (fredkinIndex N c x y s) = s := by
  have hadd : ∀ a b : Fin 2, (a + 1 ≠ b + 1) ↔ (a ≠ b) := by decide
  have hctrl : qBit c (flipBit N x (flipBit N y s)).val = qBit c s.val := by
    rw [qBit_flipBit_of_ne hcx, qBit_flipBit_of_ne hcy]
  have hxbit : qBit x (flipBit N x (flipBit N y s)).val = qBit x s.val + 1 := by
    rw [qBit_flipBit_self hxN, qBit_flipBit_of_ne hxy]
  have hybit : qBit y (flipBit N x (flipBit N y s)).val = qBit y s.val + 1 := by
    rw [qBit_flipBit_of_ne (Ne.symm hxy), qBit_flipBit_self hyN]
  have hcond : (qBit c (flipBit N x (flipBit N y s)).val = 1 ∧
      qBit x (flipBit N x (flipBit N y s)).val ≠
        qBit y (flipBit N x (flipBit N y s)).val) ↔
      (qBit c s.val = 1 ∧ qBit x s.val ≠ qBit y s.val) := by
    rw [hctrl, hxbit, hybit, hadd]
  by_cases h : qBit c s.val = 1 ∧ qBit x s.val ≠ qBit y s.val
  · rw [fredkinIndex_eq hcx hcy hxy hxN hyN s, ite_eq_left h,
      fredkinIndex_eq hcx hcy hxy hxN hyN _, ite_eq_left (hcond.mpr h)]
    have h1 : flipBit N y (flipBit N x (flipBit N y s)) =
        flipBit N x (flipBit N y (flipBit N y s)) :=
      flipBit_comm N y x (flipBit N y s)
    rw [h1, flipBit_flipBit, flipBit_flipBit]
  · rw [fredkinIndex_eq hcx hcy hxy hxN hyN s, ite_eq_right h,
      fredkinIndex_eq hcx hcy hxy hxN hyN s, ite_eq_right h]

/-- The Fredkin pullback commutes with flips at foreign qubits. -/
private theorem fredkinIndex_flipBit_comm {N c x y : ℕ} (hcx : c ≠ x) (hcy : c ≠ y)
    (hxy : x ≠ y) (hxN : x < N) (hyN : y < N) {r : ℕ} (hrc : r ≠ c) (hrx : r ≠ x)
    (hry : r ≠ y) (s : Fin (2 ^ N)) :
    fredkinIndex N c x y (flipBit N r s) = flipBit N r (fredkinIndex N c x y s) := by
  have hc : qBit c (flipBit N r s).val = qBit c s.val :=
    qBit_flipBit_of_ne (Ne.symm hrc) s
  have hx : qBit x (flipBit N r s).val = qBit x s.val :=
    qBit_flipBit_of_ne (Ne.symm hrx) s
  have hy : qBit y (flipBit N r s).val = qBit y s.val :=
    qBit_flipBit_of_ne (Ne.symm hry) s
  simp only [fredkinIndex_eq hcx hcy hxy hxN hyN]
  by_cases h : qBit c s.val = 1 ∧ qBit x s.val ≠ qBit y s.val
  · have h' : qBit c (flipBit N r s).val = 1 ∧
        qBit x (flipBit N r s).val ≠ qBit y (flipBit N r s).val := by
      rw [hc, hx, hy]
      exact h
    simp only [ite_eq_left h', ite_eq_left h]
    calc flipBit N x (flipBit N y (flipBit N r s))
        = flipBit N x (flipBit N r (flipBit N y s)) := by rw [flipBit_comm N y r s]
      _ = flipBit N r (flipBit N x (flipBit N y s)) := by
          rw [flipBit_comm N x r (flipBit N y s)]
  · have h' : ¬(qBit c (flipBit N r s).val = 1 ∧
        qBit x (flipBit N r s).val ≠ qBit y (flipBit N r s).val) := by
      rw [hc, hx, hy]
      exact h
    simp only [ite_eq_right h', ite_eq_right h]

/-- The Fredkin gate list pulls back by `fredkinIndex`. -/
private theorem applyCircuit_fredkinGates {N c x y : ℕ} (hcx : c ≠ x) (hcy : c ≠ y)
    (hxy : x ≠ y) (hcN : c < N) (hxN : x < N) (hyN : y < N)
    (ψ : Fin (2 ^ N) → ℂ) (s : Fin (2 ^ N)) :
    applyCircuit N (fredkinGates c x y) ψ s = ψ (fredkinIndex N c x y s) := by
  have hyx : y ≠ x := fun h => hxy h.symm
  have hgate : ∀ (φ : Fin (2 ^ N) → ℂ) (t : Fin (2 ^ N)),
      applyCircuit N [controlledGate xGate y x] φ t = φ (cnotIndex N y x t) := by
    intro φ t
    simp only [applyCircuit, List.foldl_cons, List.foldl_nil]
    exact applyGate_cnot hyx hyN hxN φ t
  have htoff : ∀ (φ : Fin (2 ^ N) → ℂ) (t : Fin (2 ^ N)),
      applyCircuit N (toffoliGates c x y) φ t = φ (toffoliIndex N c x y t) := by
    intro φ t
    rw [applyCircuit_toffoliGates hcx hcy hxy hcN hxN hyN]
    simp only [toffoliPerm]
  simp only [fredkinGates, fredkinIndex]
  rw [← List.singleton_append, applyCircuit_append, applyCircuit_append]
  rw [hgate, htoff, hgate]


/-- Every compute triple comes from an input and an adjacent cell pair at
or below it. -/
private theorem mem_thresholdComputeTriples {k : ℕ}
    {L : Fin (k + 1 + thresholdWork k) → ℕ} {p : ℕ × ℕ × ℕ}
    (hp : p ∈ thresholdComputeTriples k L) :
    ∃ i j, i < k ∧ j ≤ i ∧
      p = (thresholdInputPos k L i, thresholdWorkPos k L j,
        thresholdWorkPos k L (j + 1)) := by
  unfold thresholdComputeTriples at hp
  rw [List.mem_flatMap] at hp
  obtain ⟨i, hi_mem, hp_mem⟩ := hp
  rw [List.mem_range] at hi_mem
  unfold thresholdSwapTriples at hp_mem
  rw [List.mem_map] at hp_mem
  obtain ⟨j, hj_mem, hj_eq⟩ := hp_mem
  rw [List.mem_reverse, List.mem_range] at hj_mem
  exact ⟨i, j, hi_mem, by omega, hj_eq.symm⟩

/-- Every compute triple has pairwise distinct in-range components, none
the target. -/
private theorem thresholdTriple_facts {N k : ℕ}
    {L : Fin (k + 1 + thresholdWork k) → ℕ} (hL : Function.Injective L)
    (hLN : ∀ i, L i < N) {p : ℕ × ℕ × ℕ} (hp : p ∈ thresholdComputeTriples k L) :
    p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2 ∧ p.2.1 ≠ p.2.2 ∧ p.1 < N ∧ p.2.1 < N ∧ p.2.2 < N ∧
      thresholdTargetPos k L ≠ p.1 ∧ thresholdTargetPos k L ≠ p.2.1 ∧
        thresholdTargetPos k L ≠ p.2.2 := by
  obtain ⟨i, j, hi, hji, rfl⟩ := mem_thresholdComputeTriples hp

  have hjW : j < thresholdWork k := by
    simp only [thresholdWork]
    omega
  have hj1W : j + 1 < thresholdWork k := by
    simp only [thresholdWork]
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Ne.symm (thresholdWorkPos_ne_inputPos (N := N) hL hjW hi)
  · exact Ne.symm (thresholdWorkPos_ne_inputPos (N := N) hL hj1W hi)
  · intro h
    have heq := thresholdWorkPos_inj (N := N) hL hjW hj1W h
    omega
  · exact thresholdInputPos_lt hLN hi
  · exact thresholdWorkPos_lt hLN hjW
  · exact thresholdWorkPos_lt hLN hj1W
  · exact Ne.symm (thresholdInputPos_ne_targetPos (N := N) hL hi)
  · exact Ne.symm (thresholdWorkPos_ne_targetPos (N := N) hL hjW)
  · exact Ne.symm (thresholdWorkPos_ne_targetPos (N := N) hL hj1W)

/-- Every Fredkin gate is well-formed on distinct in-range qubits. -/
private theorem fredkinGates_wellFormed {N c x y : ℕ} (hcx : c ≠ x) (hcy : c ≠ y)
    (hxy : x ≠ y) (hcN : c < N) (hxN : x < N) (hyN : y < N) :
    ∀ g ∈ fredkinGates c x y, QGateWellFormed N g := by
  intro g hg
  unfold fredkinGates at hg
  simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | h | rfl
  · exact controlledGate_wellFormed xGate xGate_unitary (Ne.symm hxy) hyN hxN
  · exact toffoliGates_wellFormed hcx hcy hxy hcN hxN hyN g h
  · exact controlledGate_wellFormed xGate xGate_unitary (Ne.symm hxy) hyN hxN

/-- Flipping cells `n + 1` then `n` moves a one-hot marker from `n` to `n + 1`,
fixing everything off the work cells. -/
private theorem thresholdOneHot_move {N k : ℕ}
    {L : Fin (k + 1 + thresholdWork k) → ℕ} (hL : Function.Injective L)
    (hLN : ∀ i, L i < N) {n : ℕ} (hn : n + 1 < thresholdWork k)
    {s : Fin (2 ^ N)} (hs : thresholdOneHot N k L n s) :
    thresholdOneHot N k L (n + 1)
        (flipBit N (thresholdWorkPos k L n) (flipBit N (thresholdWorkPos k L (n + 1)) s)) ∧
      thresholdOffWorkEq N k L s
        (flipBit N (thresholdWorkPos k L n) (flipBit N (thresholdWorkPos k L (n + 1)) s)) := by
  have hn' : n < thresholdWork k := by
    simp only [thresholdWork] at hn ⊢
    omega
  have hpos_lt : ∀ j, j < thresholdWork k → thresholdWorkPos k L j < N := by
    intro j hj
    unfold thresholdWorkPos
    simp only [dite_eq_left hj]
    exact hLN _
  have hpos_inj : ∀ {j1 j2}, j1 < thresholdWork k → j2 < thresholdWork k →
      thresholdWorkPos k L j1 = thresholdWorkPos k L j2 → j1 = j2 := by
    intro j1 j2 h1 h2 heq
    unfold thresholdWorkPos at heq
    simp only [dite_eq_left h1, dite_eq_left h2] at heq
    have hFin : Fin.natAdd (k + 1) (⟨j1, h1⟩ : Fin (thresholdWork k)) =
        Fin.natAdd (k + 1) (⟨j2, h2⟩ : Fin (thresholdWork k)) := hL heq
    have hFin2 : (⟨j1, h1⟩ : Fin (thresholdWork k)) = ⟨j2, h2⟩ :=
      (Fin.natAdd_injective _ _) hFin
    exact congrArg Fin.val hFin2
  have haN : thresholdWorkPos k L n < N := hpos_lt n hn'
  have hbN : thresholdWorkPos k L (n + 1) < N := hpos_lt (n + 1) hn
  have hne_pos : thresholdWorkPos k L n ≠ thresholdWorkPos k L (n + 1) := by
    intro hcon
    have : n = n + 1 := hpos_inj hn' hn hcon
    omega
  constructor
  · unfold thresholdOneHot
    intro j hj
    by_cases hj_succ : j = n + 1
    · subst hj_succ
      have h_outer := qBit_flipBit_of_ne (Ne.symm hne_pos)
        (flipBit N (thresholdWorkPos k L (n + 1)) s)
      have h_inner := qBit_flipBit_self hbN s
      have hs_val : qBit (thresholdWorkPos k L (n + 1)) s.val = 0 := by
        have h := hs (n + 1) hn
        rw [ite_eq_right (by omega : n + 1 ≠ n)] at h
        exact h
      rw [h_outer, h_inner, hs_val, ite_eq_left rfl]
      decide
    · by_cases hj_eq : j = n
      · rw [hj_eq]
        have h_outer := qBit_flipBit_self haN
          (flipBit N (thresholdWorkPos k L (n + 1)) s)
        have h_inner := qBit_flipBit_of_ne hne_pos s
        have hs_val : qBit (thresholdWorkPos k L n) s.val = 1 := by
          have h := hs n hn'
          rw [ite_eq_left rfl] at h
          exact h
        rw [ite_eq_right (by omega : n ≠ n + 1)]
        rw [h_outer, h_inner, hs_val]
        decide
      · have hj_ne_a : thresholdWorkPos k L j ≠ thresholdWorkPos k L n := by
          intro hcon
          exact hj_eq (hpos_inj hj hn' hcon)
        have hj_ne_b : thresholdWorkPos k L j ≠ thresholdWorkPos k L (n + 1) := by
          intro hcon
          exact hj_succ (hpos_inj hj hn hcon)
        have h_outer := qBit_flipBit_of_ne hj_ne_a
          (flipBit N (thresholdWorkPos k L (n + 1)) s)
        have h_inner := qBit_flipBit_of_ne hj_ne_b s
        have hs_val : qBit (thresholdWorkPos k L j) s.val = 0 := by
          have h := hs j hj
          rw [ite_eq_right hj_eq] at h
          exact h
        rw [ite_eq_right hj_succ]
        rw [h_outer, h_inner, hs_val]
  · unfold thresholdOffWorkEq
    intro r hr
    have hr_a : r ≠ thresholdWorkPos k L n := hr n hn'
    have hr_b : r ≠ thresholdWorkPos k L (n + 1) := hr (n + 1) hn
    rw [qBit_flipBit_of_ne hr_a, qBit_flipBit_of_ne hr_b]

/-- A descending swap block with control bit `0` is the identity. -/
private theorem tripleFwd_swap_ctrl_zero {N k : ℕ}
    {L : Fin (k + 1 + thresholdWork k) → ℕ} (hL : Function.Injective L)
    (hLN : ∀ i, L i < N) (c : ℕ)
    (hc : ∀ j, j < thresholdWork k → c ≠ thresholdWorkPos k L j)
    {n : ℕ} (hn : n < thresholdWork k) {s : Fin (2 ^ N)}
    (hcs : qBit c s.val ≠ 1) :
    tripleFwd N (thresholdSwapTriples k L c n) s = s := by
  induction n generalizing s with
  | zero =>
    simp [thresholdSwapTriples, tripleFwd]
  | succ n ih =>
    have hn' : n < thresholdWork k := by
      simp only [thresholdWork] at hn ⊢
      omega
    have hsucc_lt : n + 1 < thresholdWork k := hn
    have hcons : thresholdSwapTriples k L c (n + 1) =
        (c, thresholdWorkPos k L n, thresholdWorkPos k L (n + 1)) ::
          thresholdSwapTriples k L c n := by
      unfold thresholdSwapTriples
      rw [List.range_succ, List.reverse_append]
      simp
    rw [hcons]
    have hfold : tripleFwd N
        ((c, thresholdWorkPos k L n, thresholdWorkPos k L (n + 1)) ::
          thresholdSwapTriples k L c n) s =
        tripleFwd N (thresholdSwapTriples k L c n)
          (tripleIndex N (c, thresholdWorkPos k L n, thresholdWorkPos k L (n + 1)) s) := by
      unfold tripleFwd
      rw [List.foldl_cons]
    rw [hfold]
    have hcx : c ≠ thresholdWorkPos k L n := hc n hn'
    have hcy : c ≠ thresholdWorkPos k L (n + 1) := hc (n + 1) hsucc_lt
    have hxN : thresholdWorkPos k L n < N := by
      have heq : thresholdWorkPos k L n = L (Fin.natAdd (k + 1) ⟨n, hn'⟩) := by
        simp [thresholdWorkPos, hn']
      rw [heq]
      exact hLN _
    have hyN : thresholdWorkPos k L (n + 1) < N := by
      have heq : thresholdWorkPos k L (n + 1) = L (Fin.natAdd (k + 1) ⟨n + 1, hsucc_lt⟩) := by
        simp [thresholdWorkPos, hsucc_lt]
      rw [heq]
      exact hLN _
    have hxy : thresholdWorkPos k L n ≠ thresholdWorkPos k L (n + 1) := by
      have ha_eq : thresholdWorkPos k L n = L (Fin.natAdd (k + 1) ⟨n, hn'⟩) := by
        simp [thresholdWorkPos, hn']
      have hb_eq : thresholdWorkPos k L (n + 1) = L (Fin.natAdd (k + 1) ⟨n + 1, hsucc_lt⟩) := by
        simp [thresholdWorkPos, hsucc_lt]
      rw [ha_eq, hb_eq]
      intro hEq
      have hFinEq : Fin.natAdd (k + 1) (⟨n, hn'⟩ : Fin (thresholdWork k)) =
          Fin.natAdd (k + 1) (⟨n + 1, hsucc_lt⟩ : Fin (thresholdWork k)) := hL hEq
      have hval : (Fin.natAdd (k + 1) (⟨n, hn'⟩ : Fin (thresholdWork k))).val =
          (Fin.natAdd (k + 1) (⟨n + 1, hsucc_lt⟩ : Fin (thresholdWork k))).val := by
        rw [hFinEq]
      simp only [Fin.val_natAdd] at hval
      omega
    have hhead : tripleIndex N (c, thresholdWorkPos k L n, thresholdWorkPos k L (n + 1)) s = s := by
      unfold tripleIndex
      simp only
      rw [fredkinIndex_eq hcx hcy hxy hxN hyN s]
      have hcond : ¬ (qBit c s.val = 1 ∧ qBit (thresholdWorkPos k L n) s.val ≠
          qBit (thresholdWorkPos k L (n + 1)) s.val) := by
        intro h
        exact hcs h.1
      simp [hcond]
    rw [hhead]
    exact ih hn' hcs

/-- Unfold one tripleFwd step: the head triple acts first. -/
private theorem tripleFwd_cons {N : ℕ} (h : ℕ × ℕ × ℕ) (t : List (ℕ × ℕ × ℕ))
    (s : Fin (2 ^ N)) :
    tripleFwd N (h :: t) s = tripleFwd N t (tripleIndex N h s) := rfl

/-- A descending swap block strictly below the marker is the identity. -/
private theorem tripleFwd_swap_of_lt {N k : ℕ}
    {L : Fin (k + 1 + thresholdWork k) → ℕ} (hL : Function.Injective L)
    (hLN : ∀ i, L i < N) (c : ℕ)
    (hc : ∀ j, j < thresholdWork k → c ≠ thresholdWorkPos k L j)
    {n p : ℕ} (hn : n < thresholdWork k) (hnp : n < p)
    {s : Fin (2 ^ N)} (hs : thresholdOneHot N k L p s) :
    tripleFwd N (thresholdSwapTriples k L c n) s = s := by
  revert hnp hn
  induction n with
  | zero =>
      intro hn hnp
      simp [thresholdSwapTriples, tripleFwd]
  | succ n ih =>
      intro hn hnp
      have hn_lt : n < thresholdWork k := by omega
      have hnp' : n < p := by omega
      have hsplit : thresholdSwapTriples k L c (n + 1)
          = (c, thresholdWorkPos k L n, thresholdWorkPos k L (n + 1))
            :: thresholdSwapTriples k L c n := by
        simp [thresholdSwapTriples, List.range_succ, List.reverse_append]
      have hhead : tripleIndex N (c, thresholdWorkPos k L n, thresholdWorkPos k L (n + 1)) s
          = s := by
        have hxN : thresholdWorkPos k L n < N := thresholdWorkPos_lt hLN hn_lt
        have hyN : thresholdWorkPos k L (n + 1) < N := thresholdWorkPos_lt hLN hn
        have hcx : c ≠ thresholdWorkPos k L n := hc n hn_lt
        have hcy : c ≠ thresholdWorkPos k L (n + 1) := hc (n + 1) hn
        have hxy : thresholdWorkPos k L n ≠ thresholdWorkPos k L (n + 1) := by
          intro hcon
          simp only [thresholdWorkPos, dite_eq_left hn_lt, dite_eq_left hn] at hcon
          have hinj := hL hcon
          simp only [Fin.natAdd, Fin.mk.injEq] at hinj
          omega
        have hbn : qBit (thresholdWorkPos k L n) s.val = 0 := by
          have hne : n ≠ p := by omega
          have h := hs n hn_lt
          simp [hne] at h
          exact h
        have hbn1 : qBit (thresholdWorkPos k L (n + 1)) s.val = 0 := by
          have hne : n + 1 ≠ p := by omega
          have h := hs (n + 1) hn
          simp [hne] at h
          exact h
        have hcond : ¬ (qBit c s.val = 1 ∧
            qBit (thresholdWorkPos k L n) s.val ≠ qBit (thresholdWorkPos k L (n + 1)) s.val) := by
          simp [hbn, hbn1]
        simp only [tripleIndex]
        rw [fredkinIndex_eq hcx hcy hxy hxN hyN s]
        simp [hcond]
      rw [hsplit, tripleFwd_cons, hhead]
      exact ih hn_lt hnp'

/-- The prefix count steps by the next input bit. -/
private theorem thresholdPrefixCount_succ {N k : ℕ}
    {L : Fin (k + 1 + thresholdWork k) → ℕ} {m : ℕ} (hm : m < k)
    (s : Fin (2 ^ N)) :
    thresholdPrefixCount N k L (m + 1) s =
      thresholdPrefixCount N k L m s +
        if qBit (thresholdInputPos k L m) s.val = 1 then 1 else 0 := by

  unfold thresholdPrefixCount
  simp only [Finset.card_filter]
  set a : Fin k := ⟨m, hm⟩ with ha
  have hmem : a ∈ (Finset.univ : Finset (Fin k)) := Finset.mem_univ a
  rw [← Finset.sum_erase_add _ _ hmem, ← Finset.sum_erase_add _ _ hmem]
  have hsum : ∑ x ∈ (Finset.univ : Finset (Fin k)).erase a,
        (if x.val < m + 1 ∧ qBit (thresholdInputPos k L x.val) s.val = 1 then (1 : ℕ) else 0)
      = ∑ x ∈ (Finset.univ : Finset (Fin k)).erase a,
        (if x.val < m ∧ qBit (thresholdInputPos k L x.val) s.val = 1 then (1 : ℕ) else 0) := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mem_erase] at hx
    have hval : x.val ≠ m := fun h => hx.1 (Fin.ext h)
    have heq : (x.val < m + 1 ∧ qBit (thresholdInputPos k L x.val) s.val = 1)
        ↔ (x.val < m ∧ qBit (thresholdInputPos k L x.val) s.val = 1) := by
      constructor
      · rintro ⟨hlt, hq⟩
        exact ⟨by omega, hq⟩
      · rintro ⟨hlt, hq⟩
        exact ⟨by omega, hq⟩
    simp only [heq]
  rw [hsum]
  have ha_val : a.val = m := congrArg Fin.val ha
  have hm1 : m < m + 1 := Nat.lt_succ_self m
  simp [ha_val, hm1]

/-- The empty prefix counts nothing. -/
private theorem thresholdPrefixCount_zero {N k : ℕ}
    {L : Fin (k + 1 + thresholdWork k) → ℕ} (s : Fin (2 ^ N)) :
    thresholdPrefixCount N k L 0 s = 0 := by
  unfold thresholdPrefixCount
  have h : ∀ i ∈ (Finset.univ : Finset (Fin k)),
      ¬(i.val < 0 ∧ qBit (thresholdInputPos k L i.val) s.val = 1) :=
    fun i _ hi => Nat.not_lt_zero i.val hi.1
  rw [Finset.filter_false_of_mem h, Finset.card_empty]

/-- The prefix count is at most the prefix length. -/
private theorem thresholdPrefixCount_le {N k : ℕ}
    {L : Fin (k + 1 + thresholdWork k) → ℕ} {m : ℕ}
    (s : Fin (2 ^ N)) :
    thresholdPrefixCount N k L m s ≤ m := by

  unfold thresholdPrefixCount
  have hsub : (Finset.univ.filter (fun i : Fin k =>
          i.val < m ∧ qBit (thresholdInputPos k L i.val) s.val = 1)).image Fin.val ⊆
      Finset.range m := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact Finset.mem_range.mpr hi.1
  have hinj : Function.Injective (Fin.val : Fin k → ℕ) := fun _ _ h => Fin.ext h
  calc (Finset.univ.filter (fun i : Fin k =>
            i.val < m ∧ qBit (thresholdInputPos k L i.val) s.val = 1)).card
        = ((Finset.univ.filter (fun i : Fin k =>
            i.val < m ∧ qBit (thresholdInputPos k L i.val) s.val = 1)).image Fin.val).card :=
          (Finset.card_image_of_injective _ hinj).symm
      _ ≤ (Finset.range m).card := Finset.card_le_card hsub
      _ = m := Finset.card_range m

/-- The full prefix count is the input count. -/
private theorem thresholdPrefixCount_full {N k : ℕ}
    {L : Fin (k + 1 + thresholdWork k) → ℕ} (s : Fin (2 ^ N)) :
    thresholdPrefixCount N k L k s = thresholdInputCount k L s := by
  have hid : ∀ i : Fin k, thresholdInputPos k L i.val =
      L (Fin.castAdd (thresholdWork k) (Fin.castSucc i)) := by
    intro i
    unfold thresholdInputPos
    rw [dite_eq_left i.isLt]
  unfold thresholdPrefixCount thresholdInputCount
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, hid i, i.isLt, true_and]

/-- The prefix count depends only on the input bits. -/
private theorem thresholdPrefixCount_congr {N k : ℕ}
    {L : Fin (k + 1 + thresholdWork k) → ℕ} {m : ℕ} {s s' : Fin (2 ^ N)}
    (h : ∀ i, i < k → qBit (thresholdInputPos k L i) s'.val =
      qBit (thresholdInputPos k L i) s.val) :
    thresholdPrefixCount N k L m s' = thresholdPrefixCount N k L m s := by
  unfold thresholdPrefixCount
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [h i.val i.isLt]

/-- Control set: descending swaps move the marker one cell up. -/
private theorem tripleFwd_swap_move {N k : ℕ}
    {L : Fin (k + 1 + thresholdWork k) → ℕ} (hL : Function.Injective L)
    (hLN : ∀ i, L i < N) (c : ℕ)
    (hc : ∀ j, j < thresholdWork k → c ≠ thresholdWorkPos k L j)
    {n p : ℕ} (hn : n < thresholdWork k) (hpn : p < n)
    {s : Fin (2 ^ N)} (hcs : qBit c s.val = 1) (hs : thresholdOneHot N k L p s) :
    thresholdOneHot N k L (p + 1) (tripleFwd N (thresholdSwapTriples k L c n) s) ∧
      thresholdOffWorkEq N k L s (tripleFwd N (thresholdSwapTriples k L c n) s) := by
  induction n generalizing p s with
  | zero =>
    exact absurd hpn (Nat.not_lt_zero p)
  | succ n ih =>
    have hn_n : n < thresholdWork k := by omega
    have hcons : thresholdSwapTriples k L c (n + 1) =
        (c, thresholdWorkPos k L n, thresholdWorkPos k L (n + 1)) ::
          thresholdSwapTriples k L c n := by
      simp [thresholdSwapTriples, List.range_succ, List.reverse_append]
    rw [hcons, tripleFwd_cons]
    have hcx : c ≠ thresholdWorkPos k L n := hc n hn_n
    have hcy : c ≠ thresholdWorkPos k L (n + 1) := hc (n + 1) hn
    have hxN : thresholdWorkPos k L n < N := thresholdWorkPos_lt hLN hn_n
    have hyN : thresholdWorkPos k L (n + 1) < N := thresholdWorkPos_lt hLN hn
    have hxy : thresholdWorkPos k L n ≠ thresholdWorkPos k L (n + 1) := by
      intro hcontra
      have heq : n = n + 1 := thresholdWorkPos_inj (N := N) hL hn_n hn hcontra
      omega
    have hfred : fredkinIndex N c (thresholdWorkPos k L n)
        (thresholdWorkPos k L (n + 1)) s =
        (if qBit c s.val = 1 ∧
          qBit (thresholdWorkPos k L n) s.val ≠
            qBit (thresholdWorkPos k L (n + 1)) s.val then
          flipBit N (thresholdWorkPos k L n)
            (flipBit N (thresholdWorkPos k L (n + 1)) s)
        else s) :=
      fredkinIndex_eq hcx hcy hxy hxN hyN s
    have htri : tripleIndex N (c, thresholdWorkPos k L n,
        thresholdWorkPos k L (n + 1)) s =
        fredkinIndex N c (thresholdWorkPos k L n)
          (thresholdWorkPos k L (n + 1)) s := rfl
    by_cases hp_eq : p = n
    · have hn_eq_p : n = p := hp_eq.symm
      have hb_n : qBit (thresholdWorkPos k L n) s.val = 1 := by
        have h1 := hs n hn_n
        have hif : (if n = p then (1 : Fin 2) else 0) = 1 := by simp [hn_eq_p]
        rw [hif] at h1
        exact h1

      have hb_np1 : qBit (thresholdWorkPos k L (n + 1)) s.val = 0 := by
        have h2 := hs (n + 1) hn
        have hne : n + 1 ≠ p := by omega
        simp [hne] at h2
        exact h2
      have hcond : qBit c s.val = 1 ∧
          qBit (thresholdWorkPos k L n) s.val ≠
            qBit (thresholdWorkPos k L (n + 1)) s.val := by
        refine ⟨hcs, ?_⟩
        rw [hb_n, hb_np1]
        decide
      have hhead_eq : tripleIndex N (c, thresholdWorkPos k L n,
          thresholdWorkPos k L (n + 1)) s =
          flipBit N (thresholdWorkPos k L n)
            (flipBit N (thresholdWorkPos k L (n + 1)) s) := by
        simp [htri, hfred, hcond]
      rw [hhead_eq]
      have hs_n : thresholdOneHot N k L n s := by
        have h := hs
        rw [hp_eq] at h
        exact h
      have hmove := thresholdOneHot_move hL hLN hn hs_n
      have htail : tripleFwd N (thresholdSwapTriples k L c n)
          (flipBit N (thresholdWorkPos k L n)
            (flipBit N (thresholdWorkPos k L (n + 1)) s)) =
          flipBit N (thresholdWorkPos k L n)
            (flipBit N (thresholdWorkPos k L (n + 1)) s) :=
        tripleFwd_swap_of_lt hL hLN c hc hn_n (Nat.lt_succ_self n) hmove.1
      rw [htail]
      have hp1_eq : p + 1 = n + 1 := by rw [hp_eq]
      rw [hp1_eq]
      exact hmove
    · have hpn' : p < n := by omega
      have hb_n : qBit (thresholdWorkPos k L n) s.val = 0 := by
        have h1 := hs n hn_n
        have hne1 : n ≠ p := by omega
        simp [hne1] at h1
        exact h1
      have hb_np1 : qBit (thresholdWorkPos k L (n + 1)) s.val = 0 := by
        have h2 := hs (n + 1) hn
        have hne2 : n + 1 ≠ p := by omega
        simp [hne2] at h2
        exact h2
      have hcond_false : ¬ (qBit c s.val = 1 ∧
          qBit (thresholdWorkPos k L n) s.val ≠
            qBit (thresholdWorkPos k L (n + 1)) s.val) := by
        simp [hb_n, hb_np1]
      have hhead_id : tripleIndex N (c, thresholdWorkPos k L n,
          thresholdWorkPos k L (n + 1)) s = s := by
        simp [htri, hfred, hcond_false]
      rw [hhead_id]
      exact ih hn_n hpn' hcs hs

/-- One input step: the marker advances iff the input bit is set. -/
private theorem tripleFwd_step {N k : ℕ}
    {L : Fin (k + 1 + thresholdWork k) → ℕ} (hL : Function.Injective L)
    (hLN : ∀ i, L i < N) {m p : ℕ} (hm : m < k) (hp : p ≤ m)
    {s : Fin (2 ^ N)} (hs : thresholdOneHot N k L p s) :
    thresholdOneHot N k L (p + if qBit (thresholdInputPos k L m) s.val = 1 then 1 else 0)
        (tripleFwd N (thresholdSwapTriples k L (thresholdInputPos k L m) (m + 1)) s) ∧
      thresholdOffWorkEq N k L s
        (tripleFwd N (thresholdSwapTriples k L (thresholdInputPos k L m) (m + 1)) s) := by
  by_cases h : qBit (thresholdInputPos k L m) s.val = 1
  · have hn : m + 1 < thresholdWork k := by
      unfold thresholdWork
      omega
    have hpn : p < m + 1 := Nat.lt_succ_of_le hp
    have hc : ∀ j, j < thresholdWork k → thresholdInputPos k L m ≠ thresholdWorkPos k L j :=
      fun j hj => Ne.symm (thresholdWorkPos_ne_inputPos (N := N) hL hj hm)
    have hmove := tripleFwd_swap_move hL hLN (thresholdInputPos k L m) hc hn hpn h hs
    simpa [h] using hmove
  · have hn : m + 1 < thresholdWork k := by
      unfold thresholdWork
      omega
    have hc : ∀ j, j < thresholdWork k → thresholdInputPos k L m ≠ thresholdWorkPos k L j :=
      fun j hj => Ne.symm (thresholdWorkPos_ne_inputPos (N := N) hL hj hm)
    have hid : tripleFwd N (thresholdSwapTriples k L (thresholdInputPos k L m) (m + 1)) s = s :=
      tripleFwd_swap_ctrl_zero hL hLN (thresholdInputPos k L m) hc hn h
    rw [hid]
    constructor
    · simpa [h] using hs
    · exact fun r _ => rfl

/-- Prefix invariant: after m input steps the marker sits at the prefix count. -/
private theorem tripleFwd_prefix {N k : ℕ}
    {L : Fin (k + 1 + thresholdWork k) → ℕ} (hL : Function.Injective L)
    (hLN : ∀ i, L i < N) {m : ℕ} (hm : m ≤ k)
    {s : Fin (2 ^ N)} (hs : thresholdOneHot N k L 0 s) :
    thresholdOneHot N k L (thresholdPrefixCount N k L m s)
        (tripleFwd N ((List.range m).flatMap fun i =>
          thresholdSwapTriples k L (thresholdInputPos k L i) (i + 1)) s) ∧
      thresholdOffWorkEq N k L s
        (tripleFwd N ((List.range m).flatMap fun i =>
          thresholdSwapTriples k L (thresholdInputPos k L i) (i + 1)) s) := by
  have tripleFwd_append : ∀ (l₁ l₂ : List (ℕ × ℕ × ℕ)) (t : Fin (2 ^ N)),
      tripleFwd N (l₁ ++ l₂) t = tripleFwd N l₂ (tripleFwd N l₁ t) :=
    fun l₁ l₂ t => List.foldl_append
  induction m generalizing s with
  | zero =>
    rw [List.range_zero, List.flatMap_nil, thresholdPrefixCount_zero]
    exact ⟨hs, fun r _ => rfl⟩
  | succ m ih =>
    have hm' : m < k := by omega
    have hmle : m ≤ k := by omega
    have hrange : List.range (m + 1) = List.range m ++ [m] := List.range_succ
    rw [hrange, List.flatMap_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [tripleFwd_append]
    obtain ⟨ih1, ih2⟩ := ih hmle hs
    have hle : thresholdPrefixCount N k L m s ≤ m := thresholdPrefixCount_le s

    obtain ⟨st1, st2⟩ := tripleFwd_step hL hLN hm' hle ih1
    have hbit : qBit (thresholdInputPos k L m)
          (tripleFwd N ((List.range m).flatMap fun i =>
            thresholdSwapTriples k L (thresholdInputPos k L i) (i + 1)) s).val =
        qBit (thresholdInputPos k L m) s.val :=
      ih2 _ (fun j hj => Ne.symm (thresholdWorkPos_ne_inputPos (N := N) hL hj hm'))
    have hsucc : thresholdPrefixCount N k L (m + 1) s =
          thresholdPrefixCount N k L m s +
            if qBit (thresholdInputPos k L m) s.val = 1 then 1 else 0 :=
      thresholdPrefixCount_succ hm' s
    rw [hbit] at st1
    rw [← hsucc] at st1
    refine ⟨st1, fun r hr => ?_⟩
    exact (st2 r hr).trans (ih2 r hr)

/-- Placing the marker on a clean index gives the one-hot state at cell `0`. -/
private theorem thresholdOneHot_marker {N k : ℕ}
    {L : Fin (k + 1 + thresholdWork k) → ℕ} (hL : Function.Injective L)
    (hLN : ∀ i, L i < N) {t : Fin (2 ^ N)} (ht : thresholdClean N k L t) :
    thresholdOneHot N k L 0 (flipBit N (thresholdWorkPos k L 0) t) := by
  have h0lt : 0 < thresholdWork k := by simp only [thresholdWork]; omega
  have hbit0 : ∀ (j : ℕ) (hj : j < thresholdWork k),
      qBit (thresholdWorkPos k L j) t.val = 0 := by
    intro j hj
    have hpos : thresholdWorkPos k L j = L (Fin.natAdd (k + 1) ⟨j, hj⟩) := by
      simp [thresholdWorkPos, hj]
    rw [hpos]
    exact ht ⟨j, hj⟩
  intro j hj
  by_cases hj0 : j = 0
  · simp only [hj0, ite_true]
    have hq : thresholdWorkPos k L 0 < N := by
      have h0eq : thresholdWorkPos k L 0 = L (Fin.natAdd (k + 1) ⟨0, h0lt⟩) := by
        simp [thresholdWorkPos, h0lt]
      rw [h0eq]
      exact hLN _
    have hflip := qBit_flipBit_self hq t
    rw [hflip, hbit0 0 h0lt]
    decide
  · simp only [hj0, ite_false]
    have hne : thresholdWorkPos k L j ≠ thresholdWorkPos k L 0 := by
      intro heq
      have hposj : thresholdWorkPos k L j = L (Fin.natAdd (k + 1) ⟨j, hj⟩) := by
        simp [thresholdWorkPos, hj]
      have hpos0 : thresholdWorkPos k L 0 = L (Fin.natAdd (k + 1) ⟨0, h0lt⟩) := by
        simp [thresholdWorkPos, h0lt]
      rw [hposj, hpos0] at heq
      have hinj := hL heq
      have hinj2 : (⟨j, hj⟩ : Fin (thresholdWork k)) = ⟨0, h0lt⟩ :=
        Fin.natAdd_injective _ _ hinj
      have hval : j = 0 := by simpa using congrArg Fin.val hinj2
      exact hj0 hval
    have hflip := qBit_flipBit_of_ne hne t
    rw [hflip, hbit0 j hj]


private theorem thresholdFlipIndex_oneHot_workNeTarget {k : ℕ}
    {L : Fin (k + 1 + thresholdWork k) → ℕ} (hL : Function.Injective L)
    (j : ℕ) (hj : j < thresholdWork k) :
    thresholdWorkPos k L j ≠ thresholdTargetPos k L := by
  simp only [thresholdWorkPos, thresholdTargetPos, dite_eq_left hj]
  apply hL.ne
  intro hEq
  have hVal := congrArg Fin.val hEq
  simp only [Fin.val_natAdd, Fin.val_castAdd, Fin.val_last, thresholdWork] at hVal
  omega

private theorem thresholdFlipIndex_oneHot_preserve {N : ℕ} (f : ℕ → ℕ) (tgt r : ℕ)
    (s : Fin (2 ^ N)) (js : List ℕ)
    (hne : ∀ j ∈ js, f j ≠ tgt) (hr : r ≠ tgt) :
    qBit r ((js.foldr (fun j s => cnotIndex N (f j) tgt s) s).val) = qBit r s.val := by
  induction js generalizing s with
  | nil => simp
  | cons j js ih =>
    simp only [List.foldr_cons]
    have hTail : ∀ j' ∈ js, f j' ≠ tgt := fun j' hj' => hne j' (List.mem_cons_of_mem j hj')
    have hTailPres : qBit r ((js.foldr (fun j s => cnotIndex N (f j) tgt s) s).val) =
        qBit r s.val :=
      ih s hTail

    have hUnfold : cnotIndex N (f j) tgt (js.foldr (fun j s => cnotIndex N (f j) tgt s) s) =
        (if qBit (f j) (js.foldr (fun j s => cnotIndex N (f j) tgt s) s).val = 1
          then flipBit N tgt (js.foldr (fun j s => cnotIndex N (f j) tgt s) s)
          else (js.foldr (fun j s => cnotIndex N (f j) tgt s) s)) := rfl
    rw [hUnfold]
    split_ifs with hCond
    · have h := qBit_flipBit_of_ne hr (js.foldr (fun j s => cnotIndex N (f j) tgt s) s)
      rw [h]
      exact hTailPres
    · exact hTailPres

private theorem thresholdFlipIndex_oneHot_fold {N : ℕ} (f : ℕ → ℕ) (tgt p : ℕ)
    (s : Fin (2 ^ N)) (js : List ℕ)
    (hNodup : js.Nodup)
    (hne : ∀ j ∈ js, f j ≠ tgt)
    (hread : ∀ j ∈ js, qBit (f j) s.val = (if j = p then 1 else 0)) :
    js.foldr (fun j s => cnotIndex N (f j) tgt s) s =
      if p ∈ js then flipBit N tgt s else s := by
  induction js generalizing s with
  | nil => simp
  | cons j js ih =>
    have hNodupParts := (List.nodup_cons.mp hNodup)
    have hjNotMem : j ∉ js := hNodupParts.left
    have hNodupTail : js.Nodup := hNodupParts.right
    have hneTail : ∀ j' ∈ js, f j' ≠ tgt := fun j' hj' => hne j' (List.mem_cons_of_mem j hj')
    have hreadTail : ∀ j' ∈ js, qBit (f j') s.val = (if j' = p then 1 else 0) :=
      fun j' hj' => hread j' (List.mem_cons_of_mem j hj')
    have hTailEq : js.foldr (fun j s => cnotIndex N (f j) tgt s) s =
        (if p ∈ js then flipBit N tgt s else s) :=
      ih s hNodupTail hneTail hreadTail
    have hneJ : f j ≠ tgt := hne j List.mem_cons_self
    have hReadJ : qBit (f j) s.val = (if j = p then 1 else 0) :=
      hread j List.mem_cons_self
    have hPresJ : qBit (f j) ((js.foldr (fun j s => cnotIndex N (f j) tgt s) s).val) =
        qBit (f j) s.val :=
      thresholdFlipIndex_oneHot_preserve f tgt (f j) s js hneTail hneJ
    have hReadTail : qBit (f j) ((js.foldr (fun j s => cnotIndex N (f j) tgt s) s).val) =
        (if j = p then 1 else 0) := hPresJ.trans hReadJ
    simp only [List.foldr_cons]
    by_cases hjp : j = p
    · have hOne : qBit (f j) ((js.foldr (fun j s => cnotIndex N (f j) tgt s) s).val) = 1 := by
        rw [hReadTail]
        simp [hjp]
      have hUnfold : cnotIndex N (f j) tgt (js.foldr (fun j s => cnotIndex N (f j) tgt s) s) =
          (if qBit (f j) (js.foldr (fun j s => cnotIndex N (f j) tgt s) s).val = 1
            then flipBit N tgt (js.foldr (fun j s => cnotIndex N (f j) tgt s) s)
            else (js.foldr (fun j s => cnotIndex N (f j) tgt s) s)) := rfl
      have hpNotMem : p ∉ js := by
        simp [hjp] at hjNotMem
        exact hjNotMem
      have hTailS : js.foldr (fun j s => cnotIndex N (f j) tgt s) s = s := by
        rw [hTailEq, ite_eq_right hpNotMem]
      have hpMemCons : p ∈ j :: js := by simp [hjp]
      rw [hUnfold, ite_eq_left hOne, hTailS, ite_eq_left hpMemCons]
    · have hZero : qBit (f j) ((js.foldr (fun j s => cnotIndex N (f j) tgt s) s).val) = 0 :=
        hReadTail.trans (ite_eq_right hjp)
      have hNeOne : qBit (f j) ((js.foldr (fun j s => cnotIndex N (f j) tgt s) s).val) ≠ 1 := by
        rw [hZero]
        decide
      have hUnfold : cnotIndex N (f j) tgt (js.foldr (fun j s => cnotIndex N (f j) tgt s) s) =
          (if qBit (f j) (js.foldr (fun j s => cnotIndex N (f j) tgt s) s).val = 1
            then flipBit N tgt (js.foldr (fun j s => cnotIndex N (f j) tgt s) s)
            else (js.foldr (fun j s => cnotIndex N (f j) tgt s) s)) := rfl
      rw [hUnfold, ite_eq_right hNeOne]
      by_cases hmem : p ∈ js
      · have hpMemCons : p ∈ j :: js := List.mem_cons_of_mem j hmem
        rw [hTailEq, ite_eq_left hmem, ite_eq_left hpMemCons]
      · have hpNotMemCons : p ∉ j :: js := by
          intro hCon
          rcases (List.mem_cons.mp hCon) with heq | hmem'
          · exact hjp heq.symm
          · exact hmem hmem'
        rw [hTailEq, ite_eq_right hmem, ite_eq_right hpNotMemCons]

/-- At a one-hot state the threshold flip flips the target iff the
marker is at or above the threshold. -/
private theorem thresholdFlipIndex_oneHot {N k : ℕ}
    {L : Fin (k + 1 + thresholdWork k) → ℕ} (hL : Function.Injective L)
    (hLN : ∀ i, L i < N) (T : ℕ) {p : ℕ} (hp : p < thresholdWork k)
    {s : Fin (2 ^ N)} (hs : thresholdOneHot N k L p s) :
    thresholdFlipIndex N k T L s =
      if T ≤ p then flipBit N (thresholdTargetPos k L) s else s := by
  have _ : ∀ i, L i < N := hLN
  have hNodup : (thresholdFlipCells k T).Nodup := by
    simp only [thresholdFlipCells]
    exact List.Nodup.filter _ List.nodup_range
  have hMemLt : ∀ j ∈ thresholdFlipCells k T, j < thresholdWork k := by
    intro j hj
    simp only [thresholdFlipCells, List.mem_filter, List.mem_range] at hj
    exact hj.left
  have hne : ∀ j ∈ thresholdFlipCells k T,
      thresholdWorkPos k L j ≠ thresholdTargetPos k L := by
    intro j hj
    exact thresholdFlipIndex_oneHot_workNeTarget hL j (hMemLt j hj)
  have hread : ∀ j ∈ thresholdFlipCells k T,
      qBit (thresholdWorkPos k L j) s.val = (if j = p then 1 else 0) := by
    intro j hj
    exact hs j (hMemLt j hj)
  have hFold : thresholdFlipIndex N k T L s =
      (if p ∈ thresholdFlipCells k T then flipBit N (thresholdTargetPos k L) s else s) := by
    simp only [thresholdFlipIndex]
    exact thresholdFlipIndex_oneHot_fold (fun j => thresholdWorkPos k L j)
      (thresholdTargetPos k L) p s (thresholdFlipCells k T) hNodup hne hread
  have hMemIff : p ∈ thresholdFlipCells k T ↔ T ≤ p := by
    simp only [thresholdFlipCells, List.mem_filter, List.mem_range, decide_eq_true_eq]
    constructor
    · intro h
      exact h.right
    · intro h
      exact ⟨hp, h⟩
  rw [hFold]
  by_cases hLe : T ≤ p
  · have hpMem : p ∈ thresholdFlipCells k T := hMemIff.mpr hLe
    simp [hpMem, hLe]
  · have hpNotMem : p ∉ thresholdFlipCells k T := fun h => hLe (hMemIff.mp h)
    simp [hpNotMem, hLe]

/-- On a clean index the circuit's pullback is the threshold permutation. -/
private theorem thresholdSigma_of_clean {N k : ℕ}
    {L : Fin (k + 1 + thresholdWork k) → ℕ} (hL : Function.Injective L)
    (hLN : ∀ i, L i < N) (T : ℕ) {t : Fin (2 ^ N)} (ht : thresholdClean N k L t) :
    thresholdSigma N k T L t = thresholdCounterFlip N k T L t := by
  have hj0 : 0 < thresholdWork k := by
    unfold thresholdWork
    omega
  have hs0 : thresholdOneHot N k L 0 (flipBit N (thresholdWorkPos k L 0) t) :=
    thresholdOneHot_marker hL hLN ht
  have hm : k ≤ k := le_rfl
  have hpref := tripleFwd_prefix hL hLN hm hs0
  have h_onehot : thresholdOneHot N k L
      (thresholdPrefixCount N k L k (flipBit N (thresholdWorkPos k L 0) t))
      (tripleFwd N (thresholdComputeTriples k L)
        (flipBit N (thresholdWorkPos k L 0) t)) := by
    have h1 := hpref.1
    simpa [thresholdComputeTriples] using h1
  have h_bits : ∀ i, i < k →
      qBit (thresholdInputPos k L i)
        (flipBit N (thresholdWorkPos k L 0) t).val =
      qBit (thresholdInputPos k L i) t.val := by
    intro i hi
    have hne := thresholdWorkPos_ne_inputPos (N := N) hL hj0 hi
    have hne' : thresholdInputPos k L i ≠ thresholdWorkPos k L 0 :=
      Ne.symm hne
    exact qBit_flipBit_of_ne hne' t
  have h_congr : thresholdPrefixCount N k L k
      (flipBit N (thresholdWorkPos k L 0) t) =
      thresholdPrefixCount N k L k t :=
    thresholdPrefixCount_congr (m := k) h_bits
  have h_full_t : thresholdPrefixCount N k L k t =
      thresholdInputCount k L t :=
    thresholdPrefixCount_full t
  have h_eq : thresholdPrefixCount N k L k
      (flipBit N (thresholdWorkPos k L 0) t) =
      thresholdInputCount k L t :=
    h_congr.trans h_full_t
  have h_le : thresholdInputCount k L t ≤ k := by
    unfold thresholdInputCount
    calc (Finset.univ.filter fun i : Fin k =>
            qBit (L (Fin.castAdd (thresholdWork k) (Fin.castSucc i))) t.val = 1).card
        ≤ Finset.univ.card := Finset.card_filter_le Finset.univ _
      _ = k := by rw [Finset.card_univ, Fintype.card_fin]
  have hk_lt : k < thresholdWork k := by
    unfold thresholdWork
    omega
  have hp_lt : thresholdInputCount k L t < thresholdWork k :=
    lt_of_le_of_lt h_le hk_lt
  have hp_lt' : thresholdPrefixCount N k L k
      (flipBit N (thresholdWorkPos k L 0) t) < thresholdWork k := by
    rw [h_eq]
    exact hp_lt
  have h_flip := thresholdFlipIndex_oneHot hL hLN T hp_lt' h_onehot
  rw [h_eq] at h_flip
  have h_invol : ∀ a ∈ thresholdComputeTriples k L, ∀ b : Fin (2 ^ N),
      tripleIndex N a (tripleIndex N a b) = b := by
    intro a ha b
    have hf := thresholdTriple_facts hL hLN ha
    obtain ⟨h1, h2, h3, _h4, h5, h6, _h7, _h8, _h9⟩ := hf
    unfold tripleIndex
    exact fredkinIndex_involutive h1 h2 h3 h5 h6 b
  have h_comm : ∀ a ∈ thresholdComputeTriples k L, ∀ b : Fin (2 ^ N),
      tripleIndex N a (flipBit N (thresholdTargetPos k L) b) =
        flipBit N (thresholdTargetPos k L) (tripleIndex N a b) := by
    intro a ha b
    have hf := thresholdTriple_facts hL hLN ha
    obtain ⟨h1, h2, h3, _h4, h5, h6, h7, h8, h9⟩ := hf
    unfold tripleIndex
    exact fredkinIndex_flipBit_comm h1 h2 h3 h5 h6 h7 h8 h9 b
  have h_cancel : ∀ b : Fin (2 ^ N),
      tripleBwd N (thresholdComputeTriples k L)
        (tripleFwd N (thresholdComputeTriples k L) b) = b := by
    intro b
    unfold tripleBwd tripleFwd
    exact foldr_foldl_cancel (tripleIndex N) (thresholdComputeTriples k L) h_invol b
  have h_push : ∀ b : Fin (2 ^ N),
      tripleBwd N (thresholdComputeTriples k L)
        (flipBit N (thresholdTargetPos k L) b) =
        flipBit N (thresholdTargetPos k L)
          (tripleBwd N (thresholdComputeTriples k L) b) := by
    intro b
    unfold tripleBwd
    exact foldr_comm_of_comm (tripleIndex N)
      (flipBit N (thresholdTargetPos k L)) (thresholdComputeTriples k L) h_comm b
  unfold thresholdSigma thresholdCounterFlip
  by_cases hT : T ≤ thresholdInputCount k L t
  · rw [ite_eq_left hT] at h_flip ⊢
    rw [h_flip]
    have hps := h_push (tripleFwd N (thresholdComputeTriples k L)
      (flipBit N (thresholdWorkPos k L 0) t))
    rw [hps]
    have hcs := h_cancel (flipBit N (thresholdWorkPos k L 0) t)
    rw [hcs]
    have h_target : L (Fin.castAdd (thresholdWork k) (Fin.last k)) =
        thresholdTargetPos k L := rfl
    rw [h_target]
    have h_step : flipBit N (thresholdWorkPos k L 0)
        (flipBit N (thresholdTargetPos k L)
          (flipBit N (thresholdWorkPos k L 0) t)) =
        flipBit N (thresholdTargetPos k L)
          (flipBit N (thresholdWorkPos k L 0)
            (flipBit N (thresholdWorkPos k L 0) t)) :=
      flipBit_comm N (thresholdWorkPos k L 0) (thresholdTargetPos k L) (flipBit N (thresholdWorkPos k L 0) t)

    rw [h_step]
    rw [flipBit_flipBit]
  · rw [ite_eq_right hT] at h_flip ⊢
    rw [h_flip]
    have hcs := h_cancel (flipBit N (thresholdWorkPos k L 0) t)
    rw [hcs]
    rw [flipBit_flipBit]

/-- The threshold permutation is an involution. -/
private theorem thresholdCounterFlip_involutive {N k : ℕ}
    {L : Fin (k + 1 + thresholdWork k) → ℕ} (hL : Function.Injective L)
    (T : ℕ) (t : Fin (2 ^ N)) :
    thresholdCounterFlip N k T L (thresholdCounterFlip N k T L t) = t := by
  have hcount : ∀ s : Fin (2 ^ N), thresholdInputCount k L
      (flipBit N (L (Fin.castAdd (thresholdWork k) (Fin.last k))) s) =
        thresholdInputCount k L s := by
    intro s
    simp only [thresholdInputCount]
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro i _
    have h1 : thresholdInputPos k L i.val =
        L (Fin.castAdd (thresholdWork k) (Fin.castSucc i)) :=
      thresholdInputPos_of_lt L i.isLt
    have h2 : thresholdInputPos k L i.val ≠ thresholdTargetPos k L :=
      thresholdInputPos_ne_targetPos (N := N) hL i.isLt
    rw [h1] at h2
    simp only [thresholdTargetPos] at h2
    have hbit := qBit_flipBit_of_ne (N := N) h2 s
    rw [hbit]
  by_cases h : T ≤ thresholdInputCount k L t
  · have h1 : thresholdCounterFlip N k T L t =
        flipBit N (L (Fin.castAdd (thresholdWork k) (Fin.last k))) t := by
      simp [thresholdCounterFlip, h]
    rw [h1]
    have h2 : T ≤ thresholdInputCount k L
        (flipBit N (L (Fin.castAdd (thresholdWork k) (Fin.last k))) t) := by
      rw [hcount]
      exact h
    have h3 : thresholdCounterFlip N k T L
        (flipBit N (L (Fin.castAdd (thresholdWork k) (Fin.last k))) t) =
        flipBit N (L (Fin.castAdd (thresholdWork k) (Fin.last k)))
          (flipBit N (L (Fin.castAdd (thresholdWork k) (Fin.last k))) t) := by
      simp [thresholdCounterFlip, h2]
    rw [h3]
    exact flipBit_flipBit _ _ _
  · have h1 : thresholdCounterFlip N k T L t = t := by
      simp [thresholdCounterFlip, h]
    rw [h1]
    simp [thresholdCounterFlip, h]

/-- The threshold permutation preserves clean work ancillas. -/
private theorem thresholdClean_counterFlip_iff {N k : ℕ}
    {L : Fin (k + 1 + thresholdWork k) → ℕ} (hL : Function.Injective L)
    (T : ℕ) (t : Fin (2 ^ N)) :
    thresholdClean N k L (thresholdCounterFlip N k T L t) ↔
      thresholdClean N k L t := by
  by_cases h : T ≤ thresholdInputCount k L t
  · have hflip : thresholdCounterFlip N k T L t =
        flipBit N (L (Fin.castAdd (thresholdWork k) (Fin.last k))) t := by
      simp [thresholdCounterFlip, h]
    rw [hflip]
    simp only [thresholdClean]
    constructor
    · intro hall j
      have h1 : thresholdWorkPos k L j.val = L (Fin.natAdd (k + 1) j) :=
        thresholdWorkPos_of_lt L j.isLt
      have h2 : thresholdWorkPos k L j.val ≠ thresholdTargetPos k L :=
        thresholdWorkPos_ne_targetPos (N := N) hL j.isLt
      rw [h1] at h2
      simp only [thresholdTargetPos] at h2
      have hbit := qBit_flipBit_of_ne (N := N) h2 t
      have hj := hall j
      rw [hbit] at hj
      exact hj
    · intro hall j
      have h1 : thresholdWorkPos k L j.val = L (Fin.natAdd (k + 1) j) :=
        thresholdWorkPos_of_lt L j.isLt
      have h2 : thresholdWorkPos k L j.val ≠ thresholdTargetPos k L :=
        thresholdWorkPos_ne_targetPos (N := N) hL j.isLt
      rw [h1] at h2
      simp only [thresholdTargetPos] at h2
      have hbit := qBit_flipBit_of_ne (N := N) h2 t
      have hj := hall j
      rw [hbit]
      exact hj
  · have hflip : thresholdCounterFlip N k T L t = t := by
      simp [thresholdCounterFlip, h]
    rw [hflip]

private theorem thresholdTargetPos_lt_sigma {N k : ℕ}
    {L : Fin (k + 1 + thresholdWork k) → ℕ} (hLN : ∀ i, L i < N) :
    thresholdTargetPos k L < N := by
  simp only [thresholdTargetPos]
  exact hLN _

private theorem thresholdWorkPos_lt_sigma {N k : ℕ}
    {L : Fin (k + 1 + thresholdWork k) → ℕ} (hLN : ∀ i, L i < N)
    (j : ℕ) (hj : j < thresholdWork k) :
    thresholdWorkPos k L j < N := by
  simp only [thresholdWorkPos, dite_eq_left hj]
  exact hLN _

private theorem applyCircuit_marker_singleton_sigma {N k : ℕ}
    {L : Fin (k + 1 + thresholdWork k) → ℕ} (hL : Function.Injective L)
    (hLN : ∀ i, L i < N) (ψ : Fin (2 ^ N) → ℂ) (s : Fin (2 ^ N)) :
    applyCircuit N [thresholdMarkerGate k L] ψ s =
      ψ (flipBit N (thresholdWorkPos k L 0) s) := by
  have h0 : 0 < thresholdWork k := by
    simp only [thresholdWork]
    exact Nat.zero_lt_succ k
  have hne : thresholdWorkPos k L 0 ≠ thresholdTargetPos k L :=
    thresholdWorkPos_ne_targetPos (N := N) hL h0
  have hqN : thresholdWorkPos k L 0 < N :=
    thresholdWorkPos_lt_sigma hLN 0 h0
  have hpN : thresholdTargetPos k L < N :=
    thresholdTargetPos_lt_sigma hLN
  have hsingleton : applyCircuit N [thresholdMarkerGate k L] ψ s =
      applyGate N (thresholdMarkerGate k L) ψ s := by
    simp only [applyCircuit, List.foldl_cons, List.foldl_nil]
  rw [hsingleton, thresholdMarkerGate]
  exact applyGate_embeddedGate_xGate hne hqN hpN ψ s
private theorem applyCircuit_compute_flatMap_sigma {N k : ℕ}
    {L : Fin (k + 1 + thresholdWork k) → ℕ} (hL : Function.Injective L)
    (hLN : ∀ i, L i < N) (ψ : Fin (2 ^ N) → ℂ) (s : Fin (2 ^ N)) :
    applyCircuit N ((thresholdComputeTriples k L).flatMap thresholdTripleGates) ψ s =
      ψ (tripleBwd N (thresholdComputeTriples k L) s) := by
  have hblock : ∀ p ∈ thresholdComputeTriples k L, ∀ (ψ : Fin (2 ^ N) → ℂ)
      (s : Fin (2 ^ N)),
      applyCircuit N (thresholdTripleGates p) ψ s = ψ (tripleIndex N p s) := by
    intro p hp ψ s
    obtain ⟨h1, h2, h3, h4, h5, h6, -, -, -⟩ := thresholdTriple_facts hL hLN hp
    simp only [thresholdTripleGates, tripleIndex]
    exact applyCircuit_fredkinGates h1 h2 h3 h4 h5 h6 ψ s
  have h := applyCircuit_flatMap_pullback (thresholdComputeTriples k L)
    thresholdTripleGates (tripleIndex N) hblock ψ s
  simp only [tripleBwd] at h ⊢
  exact h

private theorem applyCircuit_flip_flatMap_sigma {N k : ℕ}
    {L : Fin (k + 1 + thresholdWork k) → ℕ} (hL : Function.Injective L)
    (hLN : ∀ i, L i < N) (T : ℕ) (ψ : Fin (2 ^ N) → ℂ) (s : Fin (2 ^ N)) :
    applyCircuit N (thresholdFlipGates k T L) ψ s =
      ψ (thresholdFlipIndex N k T L s) := by
  have hblock : ∀ j ∈ thresholdFlipCells k T, ∀ (ψ : Fin (2 ^ N) → ℂ)
      (s : Fin (2 ^ N)),
      applyCircuit N
        [controlledGate xGate (thresholdWorkPos k L j) (thresholdTargetPos k L)] ψ s =
        ψ (cnotIndex N (thresholdWorkPos k L j) (thresholdTargetPos k L) s) := by
    intro j hj ψ s
    have hjrange : j ∈ List.range (thresholdWork k) := (List.mem_filter.mp hj).1
    have hjlt : j < thresholdWork k := List.mem_range.mp hjrange
    have hne : thresholdWorkPos k L j ≠ thresholdTargetPos k L :=
      thresholdWorkPos_ne_targetPos (N := N) hL hjlt
    have hcN : thresholdWorkPos k L j < N :=
      thresholdWorkPos_lt_sigma hLN j hjlt
    have htN : thresholdTargetPos k L < N :=
      thresholdTargetPos_lt_sigma hLN
    have hsingleton : applyCircuit N
        [controlledGate xGate (thresholdWorkPos k L j) (thresholdTargetPos k L)] ψ s =
        applyGate N
          (controlledGate xGate (thresholdWorkPos k L j) (thresholdTargetPos k L)) ψ s := by
      simp only [applyCircuit, List.foldl_cons, List.foldl_nil]
    rw [hsingleton]
    exact applyGate_cnot hne hcN htN ψ s
  simp only [thresholdFlipGates, thresholdFlipIndex]
  exact applyCircuit_flatMap_pullback (thresholdFlipCells k T)
    (fun j => [controlledGate xGate (thresholdWorkPos k L j) (thresholdTargetPos k L)])
    (fun j s => cnotIndex N (thresholdWorkPos k L j) (thresholdTargetPos k L) s)
    hblock ψ s
private theorem applyCircuit_revCompute_flatMap_sigma {N k : ℕ}
    {L : Fin (k + 1 + thresholdWork k) → ℕ} (hL : Function.Injective L)
    (hLN : ∀ i, L i < N) (ψ : Fin (2 ^ N) → ℂ) (s : Fin (2 ^ N)) :
    applyCircuit N
        ((thresholdComputeTriples k L).reverse.flatMap thresholdTripleGates) ψ s =
      ψ (tripleFwd N (thresholdComputeTriples k L) s) := by
  have hblock : ∀ p ∈ (thresholdComputeTriples k L).reverse,
      ∀ (ψ : Fin (2 ^ N) → ℂ) (s : Fin (2 ^ N)),
      applyCircuit N (thresholdTripleGates p) ψ s = ψ (tripleIndex N p s) := by
    intro p hp ψ s
    have hp0 : p ∈ thresholdComputeTriples k L := List.mem_reverse.mp hp
    obtain ⟨h1, h2, h3, h4, h5, h6, -, -, -⟩ := thresholdTriple_facts hL hLN hp0
    simp only [thresholdTripleGates, tripleIndex]
    exact applyCircuit_fredkinGates h1 h2 h3 h4 h5 h6 ψ s
  have h := applyCircuit_flatMap_pullback ((thresholdComputeTriples k L).reverse)
    thresholdTripleGates (tripleIndex N) hblock ψ s
  rw [List.foldr_reverse] at h
  simp only [tripleFwd] at h ⊢
  exact h

/-- The whole counter circuit pulls back by `thresholdSigma`. -/
private theorem applyCircuit_thresholdCounterGates_eq_sigma {N k : ℕ}
    {L : Fin (k + 1 + thresholdWork k) → ℕ} (hL : Function.Injective L)
    (hLN : ∀ i, L i < N) (T : ℕ) (ψ : Fin (2 ^ N) → ℂ) (t : Fin (2 ^ N)) :
    applyCircuit N (thresholdCounterGates k T L) ψ t =
      ψ (thresholdSigma N k T L t) := by
  have hmarker : ∀ (ψ : Fin (2 ^ N) → ℂ) (s : Fin (2 ^ N)),
      applyCircuit N [thresholdMarkerGate k L] ψ s =
        ψ (flipBit N (thresholdWorkPos k L 0) s) :=
    applyCircuit_marker_singleton_sigma hL hLN
  have hcompute : ∀ (ψ : Fin (2 ^ N) → ℂ) (s : Fin (2 ^ N)),
      applyCircuit N ((thresholdComputeTriples k L).flatMap thresholdTripleGates) ψ s =
        ψ (tripleBwd N (thresholdComputeTriples k L) s) :=
    applyCircuit_compute_flatMap_sigma hL hLN
  have hflip : ∀ (ψ : Fin (2 ^ N) → ℂ) (s : Fin (2 ^ N)),
      applyCircuit N (thresholdFlipGates k T L) ψ s =
        ψ (thresholdFlipIndex N k T L s) :=
    applyCircuit_flip_flatMap_sigma hL hLN T
  have hrev : ∀ (ψ : Fin (2 ^ N) → ℂ) (s : Fin (2 ^ N)),
      applyCircuit N
          ((thresholdComputeTriples k L).reverse.flatMap thresholdTripleGates) ψ s =
        ψ (tripleFwd N (thresholdComputeTriples k L) s) :=
    applyCircuit_revCompute_flatMap_sigma hL hLN
  have hcons : ∀ (a : QGate) (l : List QGate), a :: l = [a] ++ l :=
    fun a l => rfl
  simp only [thresholdCounterGates, thresholdSigma]
  rw [hcons, applyCircuit_append, applyCircuit_append, applyCircuit_append,
    applyCircuit_append, hmarker, hrev, hflip, hcompute, hmarker]
/-- The counter's basis pullback is injective. -/
private theorem thresholdSigma_injective {N k : ℕ}
    {L : Fin (k + 1 + thresholdWork k) → ℕ} (hL : Function.Injective L)
    (hLN : ∀ i, L i < N) (T : ℕ) :
    Function.Injective (thresholdSigma N k T L) := by
  have hflip : ∀ q : ℕ, Function.Injective (flipBit N q) := fun q =>
    Function.Involutive.injective (fun t => flipBit_flipBit N q t)
  have htriple : ∀ p ∈ thresholdComputeTriples k L,
      Function.Involutive (tripleIndex N p) := by
    intro p hp
    obtain ⟨d1, d2, d3, r1, r2, r3, _t1, _t2, _t3⟩ :=
      thresholdTriple_facts hL hLN hp
    change Function.Involutive (fredkinIndex N p.1 p.2.1 p.2.2)
    intro s

    exact fredkinIndex_involutive d1 d2 d3 r2 r3 s
  have hleft : Function.LeftInverse (tripleBwd N (thresholdComputeTriples k L))
      (tripleFwd N (thresholdComputeTriples k L)) :=
    foldr_foldl_cancel (f := tripleIndex N)
      (l := thresholdComputeTriples k L) htriple
  have hfwd : Function.Injective (tripleFwd N (thresholdComputeTriples k L)) :=
    Function.LeftInverse.injective hleft
  have hleft' : Function.LeftInverse (tripleFwd N (thresholdComputeTriples k L))
      (tripleBwd N (thresholdComputeTriples k L)) :=
    foldl_foldr_cancel (f := tripleIndex N)
      (l := thresholdComputeTriples k L) htriple
  have hbwd : Function.Injective (tripleBwd N (thresholdComputeTriples k L)) :=
    Function.LeftInverse.injective hleft'
  have hflipIdx : Function.Injective (thresholdFlipIndex N k T L) :=
    foldr_injective
      (f := fun j s => cnotIndex N (thresholdWorkPos k L j)
        (thresholdTargetPos k L) s) (l := thresholdFlipCells k T) (by
      intro j hj
      simp only [thresholdFlipCells, List.mem_filter, List.mem_range] at hj
      obtain ⟨hjlt, -⟩ := hj
      have hne := thresholdWorkPos_ne_targetPos (N := N) hL hjlt
      change Function.Injective
        (cnotIndex N (thresholdWorkPos k L j) (thresholdTargetPos k L))

      exact Function.Involutive.injective (fun s => cnotIndex_cnotIndex hne s))
  exact (hflip _).comp (hbwd.comp (hflipIdx.comp (hfwd.comp (hflip _))))
/-- Every counter gate is well-formed under an injective in-range layout. -/
theorem thresholdCounterGates_wellFormed {N k T : ℕ}
    {L : Fin (k + 1 + thresholdWork k) → ℕ}
    (hL : Function.Injective L) (hLN : ∀ i, L i < N) :
    ∀ g ∈ thresholdCounterGates k T L, QGateWellFormed N g := by
  have h0 : 0 < thresholdWork k := by simp only [thresholdWork]; omega
  intro g hg
  simp only [thresholdCounterGates, List.mem_cons, List.mem_append, List.mem_flatMap,
    List.mem_reverse] at hg
  rcases hg with rfl | ⟨p, hpmem, hg⟩ | hflip | ⟨p, hpmem, hg⟩ | rfl | hnil
  · exact embeddedGate_wellFormed xGate xGate_unitary
      (thresholdWorkPos_ne_targetPos (N := N) hL h0)
      (thresholdWorkPos_lt hLN h0)
      (thresholdTargetPos_lt hLN)
  · obtain ⟨hcx, hcy, hxy, hcN, hxN, hyN, -, -, -⟩ :=
      thresholdTriple_facts hL hLN hpmem
    simp only [thresholdTripleGates] at hg
    exact fredkinGates_wellFormed hcx hcy hxy hcN hxN hyN g hg
  · simp only [thresholdFlipGates, List.mem_flatMap, List.mem_singleton] at hflip
    obtain ⟨j, hjmem, rfl⟩ := hflip
    simp only [thresholdFlipCells, List.mem_filter, List.mem_range] at hjmem
    obtain ⟨hjlt, -⟩ := hjmem
    exact controlledGate_wellFormed xGate xGate_unitary
      (thresholdWorkPos_ne_targetPos (N := N) hL hjlt)
      (thresholdWorkPos_lt hLN hjlt)
      (thresholdTargetPos_lt hLN)
  · obtain ⟨hcx, hcy, hxy, hcN, hxN, hyN, -, -, -⟩ :=
      thresholdTriple_facts hL hLN hpmem
    simp only [thresholdTripleGates] at hg
    exact fredkinGates_wellFormed hcx hcy hxy hcN hxN hyN g hg
  · exact embeddedGate_wellFormed xGate xGate_unitary
      (thresholdWorkPos_ne_targetPos (N := N) hL h0)
      (thresholdWorkPos_lt hLN h0)
      (thresholdTargetPos_lt hLN)
  · simp at hnil
private lemma fredkinGates_length (c x y : ℕ) : (fredkinGates c x y).length = 7 := by
  simp [fredkinGates, toffoliGates]

private lemma thresholdTripleGates_length (p : ℕ × ℕ × ℕ) :
    (thresholdTripleGates p).length = 7 := by
  simp only [thresholdTripleGates]
  exact fredkinGates_length p.1 p.2.1 p.2.2

private lemma thresholdSwapTriples_length (k : ℕ)
    (L : Fin (k + 1 + thresholdWork k) → ℕ) (c n : ℕ) :
    (thresholdSwapTriples k L c n).length = n := by
  simp [thresholdSwapTriples]

private lemma prefix_triples_double (k : ℕ)
    (L : Fin (k + 1 + thresholdWork k) → ℕ) (F : ℕ → ℕ) (m : ℕ) :
    2 * (((List.range m).flatMap fun i => thresholdSwapTriples k L (F i) (i + 1)).length)
      = m * (m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append]
    have hlast : ([m].flatMap fun i => thresholdSwapTriples k L (F i) (i + 1)).length
        = m + 1 := by
      simp [thresholdSwapTriples_length]

    rw [hlast]
    linear_combination ih

private lemma thresholdComputeTriples_double (k : ℕ)
    (L : Fin (k + 1 + thresholdWork k) → ℕ) :
    2 * (thresholdComputeTriples k L).length = k * (k + 1) := by
  have h := prefix_triples_double k L (fun i => thresholdInputPos k L i) k
  simpa [thresholdComputeTriples] using h

private lemma thresholdFlipCells_length_le (k T : ℕ) :
    (thresholdFlipCells k T).length ≤ k + 1 := by
  have hle := List.length_filter_le (fun j => decide (T ≤ j)) (List.range (thresholdWork k))
  simp only [thresholdFlipCells] at hle ⊢
  calc (List.filter (fun j => decide (T ≤ j)) (List.range (thresholdWork k))).length
      ≤ (List.range (thresholdWork k)).length := hle
    _ = thresholdWork k := List.length_range
    _ = k + 1 := by simp only [thresholdWork]

private lemma thresholdFlipGates_length (k T : ℕ)
    (L : Fin (k + 1 + thresholdWork k) → ℕ) :
    (thresholdFlipGates k T L).length = (thresholdFlipCells k T).length := by
  simp only [thresholdFlipGates]
  have h := length_flatMap_const (thresholdFlipCells k T)
    (fun j => [controlledGate xGate (thresholdWorkPos k L j) (thresholdTargetPos k L)]) 1
    (fun x => by simp)
  rw [h]
  simp

/-- Polynomial size: at most `8 (k + 1)^2` gates. -/
theorem thresholdCounterGates_length_le (k T : ℕ)
    (L : Fin (k + 1 + thresholdWork k) → ℕ) :
    (thresholdCounterGates k T L).length ≤ 8 * (k + 1) ^ 2 := by
  have hFlat := length_flatMap_const (thresholdComputeTriples k L) thresholdTripleGates 7
    (fun x => thresholdTripleGates_length x)
  have hRev0 := length_flatMap_const ((thresholdComputeTriples k L).reverse)
    thresholdTripleGates 7 (fun x => thresholdTripleGates_length x)
  rw [List.length_reverse] at hRev0
  have hFlip := thresholdFlipGates_length k T L
  have hFlipLe := thresholdFlipCells_length_le k T
  have hCount := thresholdComputeTriples_double k L
  simp only [thresholdCounterGates, List.length_cons, List.length_append, List.length_nil,
    Nat.zero_add]
  rw [hFlat, hRev0, hFlip]
  nlinarith [hCount, hFlipLe, Nat.zero_le k, sq_nonneg k, sq_nonneg (k + 1)]

/-- **Exact basis action:** on any state supported on clean work ancillas,
the counter circuit is the threshold permutation, with no product-state
hypothesis. -/
theorem applyCircuit_thresholdCounterGates {N k T : ℕ}
    {L : Fin (k + 1 + thresholdWork k) → ℕ}
    (hL : Function.Injective L) (hLN : ∀ i, L i < N)
    (ψ : Fin (2 ^ N) → ℂ)
    (hψ : ∀ s : Fin (2 ^ N),
      (∃ j : Fin (thresholdWork k), qBit (L (Fin.natAdd (k + 1) j)) s.val = 1) →
        ψ s = 0)
    (t : Fin (2 ^ N)) :
    applyCircuit N (thresholdCounterGates k T L) ψ t =
      ψ (thresholdCounterFlip N k T L t) := by
  by_cases ht : thresholdClean N k L t
  · rw [applyCircuit_thresholdCounterGates_eq_sigma hL hLN,
      thresholdSigma_of_clean hL hLN T ht]
  · have hfin2 : ∀ x : Fin 2, x ≠ 0 → x = 1 := by decide
    have hψ' : ∀ s : Fin (2 ^ N), ¬thresholdClean N k L s → ψ s = 0 := by
      intro s hs
      apply hψ
      unfold thresholdClean at hs
      push Not at hs
      obtain ⟨j, hj⟩ := hs
      exact ⟨j, hfin2 _ hj⟩
    have hflip : ¬thresholdClean N k L (thresholdCounterFlip N k T L t) :=
      fun h => ht ((thresholdClean_counterFlip_iff hL T t).mp h)
    have hsigma : ¬thresholdClean N k L (thresholdSigma N k T L t) := by
      intro hclean
      have hv : thresholdClean N k L
          (thresholdCounterFlip N k T L (thresholdSigma N k T L t)) :=
        (thresholdClean_counterFlip_iff hL T _).mpr hclean
      have hof := thresholdSigma_of_clean hL hLN T hv
      have hinv := thresholdCounterFlip_involutive hL T (thresholdSigma N k T L t)
      have heq : thresholdSigma N k T L
            (thresholdCounterFlip N k T L (thresholdSigma N k T L t)) =
          thresholdSigma N k T L t := by rw [hof]; exact hinv
      have hinj := thresholdSigma_injective hL hLN T heq
      apply ht
      rw [← hinj]
      exact hv
    rw [applyCircuit_thresholdCounterGates_eq_sigma hL hLN, hψ' _ hsigma, hψ' _ hflip]

/-- Bridge to the QMA threshold predicate: the input count is the
acceptance count of the addressed output bits. -/
theorem thresholdInputCount_cast_eq_acceptCount {N k : ℕ}
    (L : Fin (k + 1 + thresholdWork k) → ℕ) (t : Fin (2 ^ N)) :
    (thresholdInputCount k L t : ℝ) =
      QMA.acceptCount (fun i : Fin k =>
        decide (qBit (L (Fin.castAdd (thresholdWork k) (Fin.castSucc i))) t.val = 1)) := by
  unfold thresholdInputCount QMA.acceptCount
  simp only [decide_eq_true_eq, Finset.sum_boole]

end Cslib.Complexity.Classes.QuantumGates
