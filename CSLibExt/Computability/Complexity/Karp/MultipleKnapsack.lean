/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.SubsetSumCorrect
public import CSLibExt.Computability.Complexity.Karp.SubsetSumVerify
public import CSLibExt.Computability.Complexity.PolynomialEncoding.Bounds
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

/-!
# MULTIPLE KNAPSACK is NP-complete

Items with weights and values, several knapsacks with capacities, and a target value. Each item
is assigned to at most one knapsack (assignment equal to the number of knapsacks means
omitted). The question is whether the assigned items fit in their knapsacks and have total
value at least the target.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances. The decoder accepts more than the
canonical encodings `bitEncode i` of instances: Mathlib's binary decoder of natural numbers reads
every bit list, so a correctly framed bitstring with a natural-number field ending in a false bit,
which the encoder never produces, still decodes (for example, the field `[false]` is read as `2`,
whose canonical encoding is `[false, true]`). Such a bitstring is a yes-instance exactly when the
instance it decodes to is feasible; `multipleKnapsackDec_bitEncode` covers canonical encodings.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), MULTIPLE KNAPSACK.

This module holds the definitions and the pure combinatorics of the proof:

* `fromSubsetSum_feasible`: a SUBSET-SUM instance `(as, t)` is a yes-instance exactly when the
  multiple-knapsack instance with items `(a, a)`, one knapsack of capacity `t` and target `t`
  is feasible; `reduceFromSubsetSum_correct` lifts this to bit strings.
* `multipleKnapsackDec_iff_check`: the certificate checked by the verifier machine is a list of
  one mask per knapsack, `k` bits each for `k` items (missing bits count as false, and bits after
  the last mask are ignored); an item counts as packed when one of the masks selects it.
  Overlapping masks are harmless: assigning each item to the first knapsack that selects it only
  lowers the knapsack loads.

The machines are in `MultipleKnapsackHardness` and `MultipleKnapsackVerify`, and the theorem in
`MultipleKnapsackComplete`.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipleKnapsack

open BitstringEncoding Cslib.Complexity.Karp

/-- **Multiple-knapsack instances.** A multiple-knapsack instance consists of a finite list of
items, each a pair $(w, v)$ of natural numbers giving its weight $w$ and value $v$, a finite list
of natural-number knapsack capacities, and a natural-number target value. -/
abbrev MultipleKnapsackInstance := List (ℕ × ℕ) × List ℕ × ℕ

/-- **Feasible multiple-knapsack instances.** Let a multiple-knapsack instance have items
$(w_0, v_0), \dots, (w_{k-1}, v_{k-1})$ (weight, value), knapsack capacities
$c_0, \dots, c_{m-1}$ and target $V$. The instance is feasible when there are
$a_0, \dots, a_{k-1} \in \{0, \dots, m\}$, where $a_j = b < m$ puts item $j$ in knapsack $b$
and $a_j = m$ leaves item $j$ out, such that for every $b < m$ the total weight
$\sum_{j : a_j = b} w_j$ is at most $c_b$, and the total value $\sum_{j : a_j < m} v_j$ is at
least $V$. -/
def MultipleKnapsackFeasible
    (i : MultipleKnapsackInstance) : Prop :=
  ∃ assign : List ℕ, assign.length = i.1.length ∧
    (∀ j < i.1.length, assign.getD j 0 ≤ i.2.1.length) ∧
    (∀ b < i.2.1.length,
      (Finset.range i.1.length).sum (fun j =>
        if assign.getD j 0 = b then (i.1.getD j (0, 0)).1 else 0) ≤
        i.2.1.getD b 0) ∧
    i.2.2 ≤ (Finset.range i.1.length).sum (fun j =>
      if assign.getD j 0 < i.2.1.length then (i.1.getD j (0, 0)).2 else 0)

open Classical in
/-- **MULTIPLE KNAPSACK as a decision problem.** The decision problem MULTIPLE KNAPSACK accepts a
bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding, to a feasible
multiple-knapsack instance. Bitstrings that do not decode are rejected. The decoder also reads
bitstrings that the encoder never produces: every bit list decodes to a natural number, so a
correctly framed bitstring with a natural-number field ending in a false bit decodes too, and is
accepted exactly when the instance it decodes to is feasible. -/
noncomputable def multipleKnapsackDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultipleKnapsackInstance) x with
  | some i => decide (MultipleKnapsackFeasible i)
  | none => false

/-- **MULTIPLE KNAPSACK on canonical encodings.** The decision problem MULTIPLE KNAPSACK accepts
the canonical bitstring encoding of a multiple-knapsack instance exactly when the instance is
feasible.

Source: original to this formalization. -/
@[simp] theorem multipleKnapsackDec_bitEncode (i : MultipleKnapsackInstance) :
    multipleKnapsackDec (bitEncode i) = true ↔ MultipleKnapsackFeasible i := by
  simp [multipleKnapsackDec]

/-! ### Masked sums -/

/-- A sum over item indices guarded by a mask is the sum of the masked selection. -/
private theorem sum_range_getD_eq_pick (as : List ℕ) (w : List Bool) :
    (Finset.range as.length).sum (fun j => if w.getD j false then as.getD j 0 else 0) =
      (SSVerify.pick as w).sum := by
  induction as generalizing w with
  | nil => simp [SSVerify.pick]
  | cons a as ih =>
    rw [SSVerify.sum_pick_cons, List.length_cons, Finset.sum_range_succ', add_comm]
    congr 1
    · cases w with
      | nil => simp
      | cons b w => cases b <;> simp
    · rw [← ih w.tail]
      refine Finset.sum_congr rfl fun j _ => ?_
      cases w <;> simp

/-- The mask of a decidable predicate on the first `k` indices. -/
private def predMask (k : ℕ) (p : ℕ → Prop) [DecidablePred p] : List Bool :=
  (List.range k).map fun j => decide (p j)

private theorem getD_predMask {k j : ℕ} (p : ℕ → Prop) [DecidablePred p] (hj : j < k) :
    (predMask k p).getD j false = decide (p j) := by
  simp [predMask, List.getD_eq_getElem?_getD, hj]

/-- A predicate-guarded sum over item indices is the sum of a masked selection. -/
private theorem sum_range_ite_eq_pick (as : List ℕ) (p : ℕ → Prop) [DecidablePred p] :
    (Finset.range as.length).sum (fun j => if p j then as.getD j 0 else 0) =
      (SSVerify.pick as (predMask as.length p)).sum := by
  rw [← sum_range_getD_eq_pick]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [getD_predMask p (Finset.mem_range.mp hj)]
  simp

private theorem getD_fst (l : List (ℕ × ℕ)) (j : ℕ) :
    (l.getD j (0, 0)).1 = (l.map Prod.fst).getD j 0 :=
  (List.getD_map l (0, 0) Prod.fst).symm

private theorem getD_snd (l : List (ℕ × ℕ)) (j : ℕ) :
    (l.getD j (0, 0)).2 = (l.map Prod.snd).getD j 0 :=
  (List.getD_map l (0, 0) Prod.snd).symm

/-! ### The reduction from SUBSET-SUM -/

/-- **The multiple-knapsack instance of a SUBSET-SUM instance.** For natural numbers
$a_1, \dots, a_n$ and $t$, the multiple-knapsack instance with the items $(a_1, a_1), \dots,
(a_n, a_n)$, a single knapsack of capacity $t$, and target value $t$.

Source: original to this formalization. -/
def fromSubsetSum (as : List ℕ) (t : ℕ) : MultipleKnapsackInstance :=
  (as.map fun a => (a, a), [t], t)

/-- **SUBSET-SUM instances as multiple-knapsack instances.** For natural numbers
$a_1, \dots, a_n$ and $t$, the multiple-knapsack instance with items $(a_i, a_i)$, one knapsack of
capacity $t$ and target value $t$ is feasible exactly when some sublist of $a_1, \dots, a_n$ sums
to $t$: the packed items weigh at most $t$ and are worth at least $t$, and weight equals value.

Source: original to this formalization. -/
theorem fromSubsetSum_feasible (as : List ℕ) (t : ℕ) :
    MultipleKnapsackFeasible (fromSubsetSum as t) ↔
      ∃ l : List ℕ, l.Sublist as ∧ l.sum = t := by
  have hfst : (as.map fun a => (a, a)).map Prod.fst = as := by simp [Function.comp_def]
  have hsnd : (as.map fun a => (a, a)).map Prod.snd = as := by simp [Function.comp_def]
  simp only [MultipleKnapsackFeasible, fromSubsetSum, List.length_map, List.length_singleton,
    getD_fst, getD_snd, hfst, hsnd, Nat.lt_one_iff, forall_eq, List.getD_cons_zero]
  constructor
  · rintro ⟨assign, -, -, hcap, hval⟩
    rw [sum_range_ite_eq_pick] at hcap hval
    exact ⟨_, SSVerify.pick_sublist _ _, le_antisymm hcap hval⟩
  · rintro ⟨l, hl, rfl⟩
    obtain ⟨w, hw, rfl⟩ := SSVerify.exists_pick hl
    have hget : ∀ j < as.length,
        (w.map fun b => if b then 0 else 1).getD j 0 = 0 ↔ w.getD j false = true := by
      intro j hj
      rw [List.getD_eq_getElem _ _ (by simpa [hw] using hj),
        List.getD_eq_getElem _ _ (by simpa [hw] using hj)]
      simp only [List.getElem_map]
      split <;> simp_all
    have hsum : (Finset.range as.length).sum (fun j =>
        if (w.map fun b => if b then 0 else 1).getD j 0 = 0 then as.getD j 0 else 0) =
        (SSVerify.pick as w).sum := by
      rw [← sum_range_getD_eq_pick]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [if_congr (hget j (Finset.mem_range.mp hj)) rfl rfl]
    refine ⟨w.map fun b => if b then 0 else 1, by simp [hw], fun j hj => ?_,
      hsum.le, hsum.ge⟩
    rw [List.getD_eq_getElem _ _ (by simpa [hw] using hj)]
    simp only [List.getElem_map]
    split <;> simp

/-- **Fixed no-instance of MULTIPLE KNAPSACK.** The multiple-knapsack instance with no items, no
knapsacks and target value $1$.

Source: original to this formalization. -/
def noInstance : MultipleKnapsackInstance := ([], [], 1)

/-- **The fixed no-instance is infeasible.** The instance with no items, no knapsacks and target
value $1$ is not feasible, since the empty selection has value $0$.

Source: original to this formalization. -/
theorem not_feasible_noInstance : ¬ MultipleKnapsackFeasible noInstance := by
  rintro ⟨_, _, _, _, h⟩
  simp [noInstance] at h

/-- **The SUBSET-SUM to MULTIPLE KNAPSACK map on bit strings.** A bit string that is the
SUBSET-SUM encoding of numbers $a_1, \dots, a_n$ and a target $t$ is sent to the canonical
encoding of the multiple-knapsack instance with items $(a_i, a_i)$, one knapsack of capacity $t$
and target $t$; every other bit string is sent to the encoding of the instance with no items, no
knapsacks and target $1$.

Source: original to this formalization. -/
def reduceFromSubsetSum (x : List Bool) : List Bool :=
  match SSVerify.decodeSS x with
  | some (as, t) => bitEncode (fromSubsetSum as t)
  | none => bitEncode noInstance

/-- **The SUBSET-SUM to MULTIPLE KNAPSACK map preserves answers.** For every bit string $x$,
SUBSET-SUM accepts $x$ exactly when MULTIPLE KNAPSACK accepts the image of $x$ under the
bit-string map, malformed inputs included.

Source: original to this formalization. -/
theorem reduceFromSubsetSum_correct (x : List Bool) :
    subsetSumDec x = multipleKnapsackDec (reduceFromSubsetSum x) := by
  classical
  cases hd : SSVerify.decodeSS x with
  | none =>
    have hs : subsetSumDec x = false := by
      rw [Bool.eq_false_iff, ne_eq, subsetSumDec, decide_eq_true_eq]
      rintro ⟨as, t, he, _⟩
      have := SSVerify.decodeSS_eq_some.mpr he
      rw [hd] at this
      contradiction
    rw [hs, reduceFromSubsetSum, hd]
    symm
    rw [Bool.eq_false_iff, ne_eq, multipleKnapsackDec_bitEncode]
    exact not_feasible_noInstance
  | some p =>
    obtain ⟨as, t⟩ := p
    rw [reduceFromSubsetSum, hd, Bool.eq_iff_iff, multipleKnapsackDec_bitEncode,
      fromSubsetSum_feasible, ← SSVerify.decodeSS_eq_some.mp hd,
      subsetSumDec_encodeSS_eq_true]

/-! ### The certificate check -/

/-- **Updating the unused flags.** For lists of bits $u$ (the unused flags of the items) and $w$
(the unread certificate), the new flags are $u_j \wedge \lnot w_j$ for $j < |u|$, where missing
certificate bits count as false: an item stays unused when it was unused and its bit is false.

Source: original to this formalization. -/
def orStep : List Bool → List Bool → List Bool
  | [], _ => []
  | u :: us, w => (u && !w.headD false) :: orStep us w.tail

/-- **The mask of one knapsack pass.** For lists of bits $u$ and $w$, the first $|u|$ bits of $w$,
missing bits counting as false.

Source: original to this formalization. -/
def maskTake : List Bool → List Bool → List Bool
  | [], _ => []
  | _ :: us, w => w.headD false :: maskTake us w.tail

/-- **The knapsack loop of the verifier.** For weights $w$, values $v$, a target $V$, the
remaining capacities, the unread certificate and the unused flags $u$ of the items: for each
capacity $c$ in turn, the next $|u|$ certificate bits form the mask of that knapsack, whose
selected weights must sum to at most $c$, and the selected items are no longer unused. After
the last knapsack, the values of the items that are not unused must sum to at least $V$.
When fewer than $|u|$ certificate bits remain, the missing bits count as false, and the bits left
after the mask of the last knapsack are ignored. The lists $u$, $w$ and $v$ need not have equal
lengths: weights and values at positions $j \ge |u|$ are never selected, and a position
$j < |u|$ past the end of $w$ or $v$ adds nothing to the corresponding sum.

Source: original to this formalization. -/
def loopCheck (ws vs : List ℕ) (V : ℕ) : List ℕ → List Bool → List Bool → Bool
  | [], _, u => decide (V ≤ (SSVerify.pick vs (u.map not)).sum)
  | c :: cs, w, u => decide ((SSVerify.pick ws (maskTake u w)).sum ≤ c) &&
      loopCheck ws vs V cs (w.drop u.length) (orStep u w)

/-- **The MULTIPLE KNAPSACK certificate check.** For bit strings $x$ and $w$, the check rejects
when $x$ does not decode. Otherwise $x$ decodes to items with weights $w_j$ and values $v_j$
($j < k$), capacities $c_0, \dots, c_{m-1}$ and a target $V$, and $w$ is read as $m$ masks of
$k$ bits each (missing bits false, bits after the first $mk$ ignored): the check accepts when
every mask selects weights summing to at most its knapsack's capacity and the items selected by
some mask have total value at least $V$.

Source: original to this formalization. -/
def mkCheck (x w : List Bool) : Bool :=
  match bitDecode (α := MultipleKnapsackInstance) x with
  | some (items, caps, V) =>
      loopCheck (items.map Prod.fst) (items.map Prod.snd) V caps w
        (List.replicate items.length true)
  | none => false

private theorem length_orStep : ∀ (u w : List Bool), (orStep u w).length = u.length
  | [], _ => rfl
  | _ :: us, w => by simp [orStep, length_orStep us w.tail]

private theorem maskTake_eq : ∀ (u w : List Bool),
    maskTake u w = (List.range u.length).map fun j => w.getD j false
  | [], _ => rfl
  | _ :: us, w => by
    rw [maskTake, maskTake_eq us w.tail, List.length_cons, List.range_succ_eq_map,
      List.map_cons, List.map_map]
    congr 1
    · cases w <;> rfl
    · refine List.map_congr_left fun j _ => ?_
      cases w <;> simp

private theorem getD_orStep : ∀ (u w : List Bool) (j : ℕ), j < u.length →
    (orStep u w).getD j false = (u.getD j false && !w.getD j false)
  | [], _, _, h => by simp at h
  | u :: us, w, 0, _ => by cases w <;> simp [orStep]
  | u :: us, w, j + 1, h => by
    rw [orStep, List.getD_cons_succ, getD_orStep us w.tail j (by simpa using h),
      List.getD_cons_succ]
    cases w <;> simp

/-- The `k`-bit certificate segment read in knapsack pass `i`. -/
private def segMask (w : List Bool) (k i : ℕ) : List Bool :=
  (List.range k).map fun j => w.getD (i * k + j) false

/-- The items selected by one of the first `m` segments, or already used before them. -/
private def usedMask (u w : List Bool) (k m : ℕ) : List Bool :=
  (List.range k).map fun j =>
    !u.getD j false || (List.range m).any fun i => w.getD (i * k + j) false

private theorem getD_drop (w : List Bool) (n j : ℕ) :
    (w.drop n).getD j false = w.getD (n + j) false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- The knapsack loop checks every segment against its capacity and the value of the items
selected by some segment. -/
private theorem loopCheck_iff (ws vs : List ℕ) (V k : ℕ) :
    ∀ (cs : List ℕ) (w u : List Bool), u.length = k →
      (loopCheck ws vs V cs w u = true ↔
        (∀ i < cs.length, (SSVerify.pick ws (segMask w k i)).sum ≤ cs.getD i 0) ∧
          V ≤ (SSVerify.pick vs (usedMask u w k cs.length)).sum) := by
  intro cs
  induction cs with
  | nil =>
    intro w u hu
    have he : u.map not = usedMask u w k 0 := by
      subst hu
      refine List.ext_getElem (by simp [usedMask]) fun j h₁ h₂ => ?_
      have hj : j < u.length := by simpa using h₁
      simp only [List.getElem_map, usedMask, List.getElem_range, List.range_zero,
        List.any_nil, Bool.or_false, List.getD_eq_getElem _ _ hj]
    simp [loopCheck, he]
  | cons c cs ih =>
    intro w u hu
    have hlen : (orStep u w).length = k := by rw [length_orStep, hu]
    rw [loopCheck, Bool.and_eq_true, decide_eq_true_iff, hu, ih (w.drop k) (orStep u w) hlen]
    have hseg (i : ℕ) : segMask (w.drop k) k i = segMask w k (i + 1) := by
      refine List.map_congr_left fun j _ => ?_
      rw [getD_drop]
      congr 1
      ring
    have hmask : maskTake u w = segMask w k 0 := by
      rw [maskTake_eq, hu]
      simp [segMask]
    have hused : usedMask (orStep u w) (w.drop k) k cs.length =
        usedMask u w k (cs.length + 1) := by
      refine List.map_congr_left fun j hj => ?_
      have hj' : j < u.length := by rw [hu]; exact List.mem_range.mp hj
      rw [getD_orStep u w j hj', List.range_succ_eq_map, List.any_cons, List.any_map]
      have hfun : (fun i => (w.drop k).getD (i * k + j) false) =
          ((fun i => w.getD (i * k + j) false) ∘ Nat.succ) := by
        funext i
        simp only [Function.comp_apply, getD_drop]
        congr 1
        rw [Nat.succ_eq_add_one]
        ring
      rw [hfun]
      simp only [zero_mul, zero_add]
      cases u.getD j false <;> cases w.getD j false <;> simp
    rw [hmask, hused]
    constructor
    · rintro ⟨h₀, hall, hv⟩
      refine ⟨fun i hi => ?_, hv⟩
      cases i with
      | zero => simpa using h₀
      | succ i => simpa [hseg] using hall i (by simpa using hi)
    · rintro ⟨hall, hv⟩
      refine ⟨by simpa using hall 0 (by simp), fun i hi => ?_, hv⟩
      simpa [hseg] using hall (i + 1) (by simpa using hi)

/-- **Soundness of the certificate check.** A certificate passing the knapsack loop, started
with every item unused, yields a feasible assignment: each item goes to the first knapsack
whose mask selects it. -/
private theorem feasible_of_loopCheck (items : List (ℕ × ℕ)) (caps : List ℕ) (V : ℕ) (w : List Bool)
    (hw : loopCheck (items.map Prod.fst) (items.map Prod.snd) V caps w
      (List.replicate items.length true) = true) :
    MultipleKnapsackFeasible (items, caps, V) := by
  classical
  set k := items.length with hk
  set m := caps.length with hm
  have hws : (items.map Prod.fst).length = k := by simp [hk]
  have hvs : (items.map Prod.snd).length = k := by simp [hk]
  have hcheck (w : List Bool) := loopCheck_iff (items.map Prod.fst) (items.map Prod.snd) V k
    caps w (List.replicate k true) (by simp)
  have hused (w : List Bool) : usedMask (List.replicate k true) w k m =
      (List.range k).map fun j => (List.range m).any fun i => w.getD (i * k + j) false := by
    refine List.map_congr_left fun j hj => ?_
    rw [List.getD_eq_getElem _ _ (by simpa using List.mem_range.mp hj)]
    simp
  simp only [MultipleKnapsackFeasible, getD_fst, getD_snd]
  obtain ⟨hcap, hval⟩ := (hcheck w).mp hw
  let sel : ℕ → Prop := fun j => ∃ i, i < m ∧ w.getD (i * k + j) false = true
  let first : ℕ → ℕ := fun j => if h : sel j then Nat.find h else m
  have hfirst_le (j : ℕ) : first j ≤ m := by
    simp only [first]
    split
    · exact (Nat.find_spec ‹sel j›).1.le
    · exact le_rfl
  have hfirst_lt (j : ℕ) : first j < m ↔ sel j := by
    simp only [first]
    split
    · exact ⟨fun _ => ‹_›, fun _ => (Nat.find_spec ‹sel j›).1⟩
    · exact ⟨fun h => absurd h (lt_irrefl _), fun h => absurd h ‹_›⟩
  have hfirst_eq (j b : ℕ) (hb : b < m) (h : first j = b) :
      w.getD (b * k + j) false = true := by
    have hs : sel j := (hfirst_lt j).mp (h ▸ hb)
    simp only [first, hs, ↓reduceDIte] at h
    subst h
    exact (Nat.find_spec hs).2
  let assign := (List.range k).map first
  have hassign (j : ℕ) (hj : j < k) : assign.getD j 0 = first j := by
    rw [List.getD_eq_getElem _ _ (by simpa [assign] using hj)]
    simp [assign]
  refine ⟨assign, by simp [assign, hk], fun j hj => by rw [hassign j hj]; exact hfirst_le j,
    fun b hb => ?_, ?_⟩
  · calc (Finset.range k).sum (fun j =>
          if assign.getD j 0 = b then (items.map Prod.fst).getD j 0 else 0)
        ≤ (Finset.range k).sum (fun j =>
          if (segMask w k b).getD j false then (items.map Prod.fst).getD j 0 else 0) := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hj' := Finset.mem_range.mp hj
          rw [hassign j hj']
          by_cases h : first j = b
          · have hs : (segMask w k b).getD j false = true := by
              rw [List.getD_eq_getElem _ _ (by simpa [segMask] using hj')]
              simpa [segMask] using hfirst_eq j b hb h
            simp only [h, hs, ↓reduceIte, le_refl]
          · simp only [h, ↓reduceIte, Nat.zero_le]
      _ = (SSVerify.pick (items.map Prod.fst) (segMask w k b)).sum := by
          rw [← sum_range_getD_eq_pick, hws]
      _ ≤ caps.getD b 0 := hcap b hb
  · refine hval.trans (le_of_eq ?_)
    rw [hused, ← sum_range_getD_eq_pick, hvs]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.mp hj
    rw [hassign j hj', List.getD_eq_getElem _ _ (by simpa using hj')]
    simp only [List.getElem_map, List.getElem_range]
    have hiff : ((List.range m).any fun i => w.getD (i * k + j) false) = true ↔
        first j < m := by
      rw [hfirst_lt j]
      simp [sel]
    rw [← hm]
    by_cases hs : first j < m
    · simp only [hs, hiff.mpr hs, ↓reduceIte]
    · have hn : ((List.range m).any fun i => w.getD (i * k + j) false) = false := by
        simpa using fun h => hs (hiff.mp h)
      simp only [hs, hn, ↓reduceIte, Bool.false_eq_true]

/-- **Completeness of the certificate check.** A feasible assignment gives a certificate of
$m k$ bits, for $m$ knapsacks and $k$ items, that passes the knapsack loop started with every
item unused: the mask of knapsack $b$ selects the items assigned to $b$. -/
private theorem exists_loopCheck_of_feasible (items : List (ℕ × ℕ)) (caps : List ℕ) (V : ℕ)
    (h : MultipleKnapsackFeasible (items, caps, V)) :
    ∃ w : List Bool, w.length ≤ caps.length * items.length ∧
      loopCheck (items.map Prod.fst) (items.map Prod.snd) V caps w
        (List.replicate items.length true) = true := by
  classical
  set k := items.length with hk
  set m := caps.length with hm
  have hws : (items.map Prod.fst).length = k := by simp [hk]
  have hvs : (items.map Prod.snd).length = k := by simp [hk]
  have hcheck (w : List Bool) := loopCheck_iff (items.map Prod.fst) (items.map Prod.snd) V k
    caps w (List.replicate k true) (by simp)
  have hused (w : List Bool) : usedMask (List.replicate k true) w k m =
      (List.range k).map fun j => (List.range m).any fun i => w.getD (i * k + j) false := by
    refine List.map_congr_left fun j hj => ?_
    rw [List.getD_eq_getElem _ _ (by simpa using List.mem_range.mp hj)]
    simp
  simp only [MultipleKnapsackFeasible, getD_fst, getD_snd] at h
  obtain ⟨assign, hlen, hle, hcap, hval⟩ := h
  let w := (List.range (m * k)).map fun n => decide (assign.getD (n % k) 0 = n / k)
  have hw (i j : ℕ) (hi : i < m) (hj : j < k) :
      w.getD (i * k + j) false = decide (assign.getD j 0 = i) := by
    have hn : i * k + j < m * k := by nlinarith
    rw [List.getD_eq_getElem _ _ (by simpa [w] using hn)]
    simp only [w, List.getElem_map, List.getElem_range]
    have hk0 : 0 < k := by omega
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj,
      Nat.add_mul_div_right _ _ hk0, Nat.div_eq_of_lt hj, Nat.zero_add]
  refine ⟨w, by simp [w], (hcheck w).mpr ⟨fun i hi => ?_, ?_⟩⟩
  · have hseg : segMask w k i = predMask k fun j => assign.getD j 0 = i := by
      refine List.map_congr_left fun j hj => ?_
      rw [hw i j hi (List.mem_range.mp hj)]
    rw [hseg, ← hws, ← sum_range_ite_eq_pick, hws]
    exact hcap i hi
  · rw [hused]
    have hmask : ((List.range k).map fun j =>
        (List.range m).any fun i => w.getD (i * k + j) false) =
        predMask k fun j => assign.getD j 0 < m := by
      refine List.map_congr_left fun j hj => ?_
      have hj' := List.mem_range.mp hj
      rw [Bool.eq_iff_iff, decide_eq_true_iff, List.any_eq_true]
      simp only [List.mem_range]
      constructor
      · rintro ⟨i, hi, h⟩
        rw [hw i j hi hj', decide_eq_true_eq] at h
        omega
      · intro h
        exact ⟨_, h, by rw [hw _ j h hj', decide_eq_true_eq]⟩
    rw [hmask, ← hvs, ← sum_range_ite_eq_pick, hvs]
    exact hval

/-- **Certificates for multiple-knapsack instances.** A multiple-knapsack instance with $k$ items
and $m$ knapsacks is feasible exactly when some certificate of at most $m k$ bits passes the
knapsack loop of the certificate check started with every item unused. A feasible assignment
gives the masks of the items assigned to each knapsack; conversely, overlapping masks are
harmless, since assigning each item to the first knapsack whose mask selects it only lowers the
knapsack loads.

Source: original to this formalization. -/
theorem feasible_iff_exists_loopCheck (items : List (ℕ × ℕ)) (caps : List ℕ) (V : ℕ) :
    MultipleKnapsackFeasible (items, caps, V) ↔
      ∃ w : List Bool, w.length ≤ caps.length * items.length ∧
        loopCheck (items.map Prod.fst) (items.map Prod.snd) V caps w
          (List.replicate items.length true) = true :=
  ⟨exists_loopCheck_of_feasible items caps V, fun ⟨w, _, hw⟩ =>
    feasible_of_loopCheck items caps V w hw⟩

/-- **MULTIPLE KNAPSACK is characterized by its certificate check.** A bit string $x$ is a
yes-instance of MULTIPLE KNAPSACK exactly when some certificate $w$ with $|w| \le |x|^2$ passes the
certificate check.

Source: original to this formalization. -/
theorem multipleKnapsackDec_iff_check (x : List Bool) :
    multipleKnapsackDec x = true ↔ ∃ w : List Bool, w.length ≤ x.length ^ 2 ∧
      mkCheck x w = true := by
  cases hd : bitDecode (α := MultipleKnapsackInstance) x with
  | none => simp [multipleKnapsackDec, mkCheck, hd]
  | some i =>
    obtain ⟨items, caps, V⟩ := i
    have hk : items.length ≤ x.length :=
      Cslib.Complexity.PolynomialEncoding.decoded_fst_list_length_le hd
    have hm : caps.length ≤ x.length :=
      Cslib.Complexity.PolynomialEncoding.decoded_middle_list_length_le hd
    simp only [multipleKnapsackDec, mkCheck, hd, decide_eq_true_eq]
    constructor
    · intro h
      obtain ⟨w, hw, hc⟩ := exists_loopCheck_of_feasible items caps V h
      exact ⟨w, hw.trans (by rw [sq]; exact Nat.mul_le_mul hm hk), hc⟩
    · rintro ⟨w, -, hc⟩
      exact feasible_of_loopCheck items caps V w hc

end MetaMathlibExt.Complexity.NPComplete.MultipleKnapsack
