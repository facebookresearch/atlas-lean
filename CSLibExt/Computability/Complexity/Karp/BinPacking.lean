/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BIN PACKING is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), BIN PACKING; D. S.
Johnson, "Fast algorithms for bin packing" (1974).
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
import CSLibExt.Computability.Complexity.Karp.PartitionComplete
import CSLibExt.Computability.Complexity.PolynomialEncoding.Copy
import CSLibExt.Computability.Complexity.PolynomialEncoding.Frame
import CSLibExt.Computability.Complexity.PolynomialEncoding.NatPair
import CSLibExt.Computability.Complexity.PolynomialEncoding.PairSplit
import CSLibExt.Computability.Complexity.PolynomialEncoding.UnaryNat

/-!
# BIN PACKING is NP-complete

A list of item sizes, a bin capacity, and a number `K` of bins. The question is whether all
items fit into at most `K` bins of the given capacity, witnessed by a partition of the items
into exactly `K` bins (empty bins allowed).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).

The proof reduces binary PARTITION to two bins and verifies certificates consisting of one
selection mask per used bin.
-/

namespace MetaMathlibExt.Complexity.NPComplete.BinPacking

@[expose] public section

/-- **Bin packing instances.** An instance of BIN PACKING is a triple $(s, B, K)$ of a finite
list $s$ of natural numbers (the item sizes), a natural number $B$ (the bin capacity) and a
natural number $K$ (the number of bins). -/
abbrev BinPackingInstance := List ℕ × ℕ × ℕ

/-- **Feasible bin packing instances.** An instance $(s, B, K)$ of BIN PACKING is feasible when
there is a list of exactly $K$ bins, each a finite list of natural numbers with sum at most $B$,
such that the concatenation of the bins is a permutation of $s$.

Since bins may be empty, this says that the items fit into at most $K$ bins of capacity $B$. -/
def BinPackingFeasible
    (i : BinPackingInstance) : Prop :=
  ∃ bins : List (List ℕ), bins.length = i.2.2 ∧ bins.flatten.Perm i.1 ∧
    ∀ bin ∈ bins, bin.sum ≤ i.2.1

open Classical in
/-- **The bin packing decision problem.** BIN PACKING is the decision problem that accepts a
bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of bin packing
instances, to a feasible instance; it rejects every bitstring that fails to decode. -/
noncomputable def binPackingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := BinPackingInstance) x with
  | some i => decide (BinPackingFeasible i)
  | none => false

end

open BitstringEncoding

private theorem sublist_complement {α : Type} {s a : List α} (hs : s.Sublist a) :
    ∃ r, (s ++ r).Perm a := by
  induction hs with
  | slnil => exact ⟨[], .rfl⟩
  | @cons s a x _ ih =>
    obtain ⟨r, hr⟩ := ih
    exact ⟨x :: r, List.perm_middle.trans (hr.cons x)⟩
  | cons_cons x _ ih =>
    obtain ⟨r, hr⟩ := ih
    exact ⟨r, hr.cons x⟩

private theorem two_bins (as : List ℕ) :
    BinPackingFeasible (as.map (· * 2), as.sum, 2) ↔ Partition.PartitionFeasible as := by
  rw [Partition.feasible_iff_doubled_sublist]
  constructor
  · rintro ⟨bins, hlen, hperm, hcap⟩
    obtain ⟨b₁, b₂, rfl⟩ : ∃ b₁ b₂, bins = [b₁, b₂] := by
      match bins with
      | [b₁, b₂] => exact ⟨b₁, b₂, rfl⟩
      | [] | [_] | _ :: _ :: _ :: _ => simp at hlen
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at hperm
    have sum₁ := hcap b₁ (by simp)
    have sum₂ := hcap b₂ (by simp)
    have htotal := hperm.sum_eq
    rw [List.sum_append] at htotal
    have hd : (as.map (· * 2)).sum = as.sum * 2 := by
      simpa using List.sum_map_mul_right as id 2
    obtain ⟨s, hp, hs⟩ := List.exists_perm_sublist (List.sublist_append_left b₁ b₂) hperm
    have hss := hp.sum_eq
    exact ⟨s, hs, by dsimp at sum₁ sum₂; omega⟩
  · rintro ⟨s, hs, he⟩
    obtain ⟨r, hr⟩ := sublist_complement hs
    have hd : (as.map (· * 2)).sum = as.sum * 2 := by
      simpa using List.sum_map_mul_right as id 2
    have ht := hr.sum_eq
    rw [List.sum_append] at ht
    refine ⟨[s, r], rfl, by simpa using hr, ?_⟩
    intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl <;> dsimp <;> omega

private theorem short_bins (i : BinPackingInstance) :
    BinPackingFeasible i ↔
      ∃ bins : List (List ℕ), bins.length ≤ i.2.2 ∧ bins.length ≤ i.1.length ∧
        bins.flatten.Perm i.1 ∧ ∀ bin ∈ bins, bin.sum ≤ i.2.1 := by
  have prune (bins : List (List ℕ)) :
      ∃ bs : List (List ℕ), bs.Sublist bins ∧ bs.flatten = bins.flatten ∧
        bs.length ≤ bins.flatten.length := by
    induction bins with
    | nil => exact ⟨[], .slnil, rfl, le_rfl⟩
    | cons b bins ih =>
      obtain ⟨bs, hsub, hflat, hlen⟩ := ih
      cases b with
      | nil => exact ⟨bs, hsub.cons [], by simpa using hflat, by simpa using hlen⟩
      | cons a b =>
        refine ⟨(a :: b) :: bs, hsub.cons_cons _, by simp [hflat], ?_⟩
        simp only [List.length_cons, List.flatten_cons, List.cons_append, List.length_append]
        omega
  constructor
  · rintro ⟨bins, hk, hp, hcap⟩
    obtain ⟨bs, hsub, hflat, hlen⟩ := prune bins
    exact ⟨bs, hsub.length_le.trans_eq hk, hlen.trans_eq hp.length_eq,
      hflat.symm ▸ hp, fun b hb => hcap b (hsub.subset hb)⟩
  · rintro ⟨bins, hk, _, hp, hcap⟩
    have emp (n : ℕ) : (List.replicate n ([] : List ℕ)).flatten = [] := by
      induction n with
      | zero => rfl
      | succ n ih => simp [List.replicate_succ, ih]
    refine ⟨bins ++ List.replicate (i.2.2 - bins.length) [], ?_,
      by simpa [emp] using hp, ?_⟩
    · simp; omega
    · intro b hb
      rcases List.mem_append.mp hb with hb | hb
      · exact hcap b hb
      · have he := List.eq_of_mem_replicate hb
        simp [he]

-- The PARTITION reduction already computes the doubled items and their target sum.
-- The remaining machine rearranges these fields into a BIN PACKING instance.
namespace Hardness

open Turing Function TM2Program TM2Embedding ComplexityTheory
open Cslib.Complexity Cslib.Complexity.Karp Cslib.Complexity.PolynomialEncoding

private def convert (x : List Bool) : List Bool :=
  match undelimit x with
  | some (p, r) =>
    if r.isEmpty && !p.isEmpty then []
    else delimit r ++ delimit p ++ Computability.encodeNat 2
  | none => []

private theorem correct (x : List Bool) :
    Partition.partitionDec x = binPackingDec (convert (Partition.reduceToSubsetSum x)) := by
  classical
  cases hd : bitDecode (α := List ℕ) x with
  | none =>
    rw [Partition.partitionDec, Partition.reduceToSubsetSum, hd]
    rfl
  | some as =>
    have hr : (encodeSS (as.map (· * 2)) as.sum) =
        delimit (Computability.encodeNat as.sum) ++ bitEncode (as.map (· * 2)) := by
      simp only [encodeSS, List.flatMap_def]
      change _ = delimit (Computability.encodeNat as.sum) ++
        (((as.map (· * 2)).map Computability.encodeNat).map delimit).flatten
      simp only [List.map_map, Function.comp_def]
    have hn' : ((bitEncode (as.map (· * 2))).isEmpty &&
        !(Computability.encodeNat as.sum).isEmpty) = false := by
      cases as with
      | nil => rfl
      | cons a as =>
        change (((((a * 2 :: as.map (· * 2)).map Computability.encodeNat).map
          delimit).flatten).isEmpty && _) = false
        simp only [List.map_cons, List.flatten_cons, List.isEmpty_append]
        have h : (delimit (Computability.encodeNat (a * 2))).isEmpty = false := by
          generalize Computability.encodeNat (a * 2) = p
          cases p <;> rfl
        rw [h]
        rfl
    have he : delimit (bitEncode (as.map (· * 2))) ++
          delimit (Computability.encodeNat as.sum) ++ Computability.encodeNat 2 =
        bitEncode (α := BinPackingInstance) (as.map (· * 2), as.sum, 2) := by
      rw [List.append_assoc]
      change _ = delimit (bitEncode (as.map (· * 2))) ++
        (delimit (bitEncode as.sum) ++ bitEncode (2 : ℕ))
      simp only [BinaryNatEncoding.bitEncode_nat]
    rw [Partition.partitionDec, hd, Partition.reduceToSubsetSum, hd]
    change decide (Partition.PartitionFeasible as) =
      binPackingDec (convert (encodeSS (as.map (· * 2)) as.sum))
    rw [convert, hr, undelimit_delimit]
    simp only [hn', Bool.false_eq_true, ↓reduceIte, he, binPackingDec, bitDecode_bitEncode]
    rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
    exact (two_bins as).symm

private abbrev K := PairSplit.K ⊕ Bool

private abbrev Lab := PairSplit.Lab ⊕ Fin 7

private def emb : SEmb (fun _ : PairSplit.K => Bool) (fun _ : K => Bool) where
  e := Sum.inl
  inj _ _ := Sum.inl.inj
  ι _ := Equiv.refl Bool

private def redirect : PairSplit.Lab → Lab
  | .good => .inr 0
  | .bad => .inr 6
  | l => .inl l

private def prog : Lab → TM2.Stmt (fun _ : K => Bool) Lab Bool
  | .inl l => mapS emb redirect (PairSplit.prog l)
  | .inr 0 => .peek (.inl .input) (fun _ o => o.isNone) <| .branch id
    (.peek (.inl .left) (fun _ o => o.isSome) <| .branch id
      (.goto fun _ => .inr 6) (.goto fun _ => .inr 1))
    (.goto fun _ => .inr 1)
  | .inr 1 => emitR (.inr true) (Computability.encodeNat 2) (.inr 2)
  | .inr 2 => emitFrame (.inl .left) (.inr false) some id (.inr 2) (.inr 3)
  | .inr 3 => moveB (.inr false) (.inr true) some id (.inr 3) (.inr 4)
  | .inr 4 => emitFrame (.inl .input) (.inr false) some id (.inr 4) (.inr 5)
  | .inr 5 => moveB (.inr false) (.inr true) some id (.inr 5) (.inr 6)
  | .inr _ => .halt

private theorem embeds : Embeds emb redirect PairSplit.prog prog := by
  intro l
  cases l with
  | good | bad => exact Or.inr rfl
  | read | copy => exact Or.inl rfl

private theorem run_frames (S : K → List Bool) (p r : List Bool) (v : Bool)
    (hp : S (.inl .left) = p) (hr : S (.inl .input) = r)
    (ht : S (.inr false) = []) (ho : S (.inr true) = []) :
    ∃ w T, RunLe prog (5 * (p.length + r.length) + 20) ⟨some (.inr 1), v, S⟩
      ⟨some (.inr 6), w, T⟩ ∧
      T (.inr true) = delimit r ++ delimit p ++ Computability.encodeNat 2 := by
  let S₀ := update S (.inr true) (Computability.encodeNat 2)
  have h₀ : Run prog 1 ⟨some (.inr 1), v, S⟩ ⟨some (.inr 2), v, S₀⟩ := by
    simpa [S₀, ho] using
      (emitR_run (M := prog) (self := Sum.inr 1) (next := Sum.inr 2)
        (k := Sum.inr true) (ys := Computability.encodeNat 2) rfl v S)
  obtain ⟨S₁, h₁, _, ht₁, hf₁⟩ := emitFrame_run
    (M := prog) (self := Sum.inr 2) (next := Sum.inr 3)
    (a := Sum.inl .left) (b := Sum.inr false) (d := some) (g := id)
    rfl (by decide) id (fun _ => rfl) p [] v S₀ rfl (by simp [S₀, hp])
  have ht₁' : S₁ (.inr false) = (delimit p).reverse := by simpa [S₀, ht] using ht₁
  obtain ⟨v₂, S₂, h₂, ht₂, ho₂, hf₂⟩ := moveB_run
    (M := prog) (self := Sum.inr 3) (next := Sum.inr 4)
    (a := Sum.inr false) (b := Sum.inr true) (d := some) (g := id)
    rfl (by decide) (delimit p).reverse (delimit p).reverse [] false S₁
    (by simpa using ht₁') (by simp [IsBitBlock]) rfl
  have ho₂' : S₂ (.inr true) = delimit p ++ Computability.encodeNat 2 := by
    rw [hf₁ (.inr true) (by decide) (by decide)] at ho₂
    simpa [S₀] using ho₂
  have hr₂ : S₂ (.inl .input) = r := by
    rw [hf₂ _ (by decide) (by decide), hf₁ _ (by decide) (by decide)]
    simpa [S₀] using hr
  obtain ⟨S₃, h₃, _, ht₃, hf₃⟩ := emitFrame_run
    (M := prog) (self := Sum.inr 4) (next := Sum.inr 5)
    (a := Sum.inl .input) (b := Sum.inr false) (d := some) (g := id)
    rfl (by decide) id (fun _ => rfl) r [] v₂ S₂ rfl (by simpa using hr₂)
  obtain ⟨v₄, S₄, h₄, _, ho₄, _⟩ := moveB_run
    (M := prog) (self := Sum.inr 5) (next := Sum.inr 6)
    (a := Sum.inr false) (b := Sum.inr true) (d := some) (g := id)
    rfl (by decide) (delimit r).reverse (delimit r).reverse [] false S₃
    (by simpa [ht₂] using ht₃) (by simp [IsBitBlock]) rfl
  refine ⟨v₄, S₄, ((((h₀.trans h₁).trans h₂).trans h₃).trans h₄).le ?_, ?_⟩
  · simp only [List.length_reverse, length_delimit]
    omega
  · simpa [hf₃ (.inr true) (by decide) (by decide), ho₂', List.append_assoc] using ho₄

private theorem run (x : List Bool) :
    ∃ v S, RunLe prog (10 * (x.length + 1) + 20)
      ⟨some (.inl .read), false, update (fun _ => []) (.inl .input) x⟩
      ⟨some (.inr 6), v, S⟩ ∧ S (.inr true) = convert x := by
  let S₀ : K → List Bool := update (fun _ => []) (.inl .input) x
  have h₀ : Agree emb (PairSplit.st x [] []) S₀ := by
    intro k
    cases k <;> simp [emb, S₀, PairSplit.st]
  obtain ⟨v, S, h, hf, ha⟩ := PairSplit.run_embedded emb redirect embeds x false S₀ h₀
  have ht : S (.inr false) = [] := by
    simpa [S₀] using hf (.inr false) (by simp [emb])
  have ho : S (.inr true) = [] := by
    simpa [S₀] using hf (.inr true) (by simp [emb])
  cases hd : undelimit x with
  | none =>
    refine ⟨v, S, ?_, by simp [convert, hd, ho]⟩
    simp only [hd, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, redirect] at h
    exact h.mono (by omega)
  | some pr =>
    obtain ⟨p, r⟩ := pr
    simp only [hd, Option.isSome_some, ↓reduceIte, redirect] at h
    have hp : S (.inl .left) = p := by
      simpa [emb, PairSplit.st] using ha p r hd .left
    have hr : S (.inl .input) = r := by
      simpa [emb, PairSplit.st] using ha p r hd .input
    let reject := r.isEmpty && !p.isEmpty
    let v₁ := if r.isEmpty then !p.isEmpty else false
    have hcheck : Run prog 1 ⟨some (.inr 0), v, S⟩
        ⟨some (.inr (if reject then 6 else 1)), v₁, S⟩ := by
      apply Run.single
      cases p <;> cases r <;> simp [prog, TM2.stepAux, hp, hr, reject, v₁]
    cases he : reject with
    | true =>
      rw [he] at hcheck
      refine ⟨v₁, S, (h.trans (hcheck.le le_rfl)).mono (by omega), ?_⟩
      rw [convert, hd]
      change S (Sum.inr true) = if reject then _ else _
      rw [he]
      exact ho
    | false =>
      rw [he] at hcheck
      obtain ⟨w, T, hn, hout⟩ := run_frames S p r v₁ hp hr ht ho
      refine ⟨w, T, ((h.trans (hcheck.le le_rfl)).trans hn).mono ?_, ?_⟩
      · have hx := (Cslib.CookLevin.undelimit_eq_some_iff _ _ _).mp hd
        rw [hx, List.length_append, length_delimit]
        omega
      · rw [convert, hd]
        change T (Sum.inr true) = if reject then _ else _
        rw [he]
        exact hout

private noncomputable def comp : Host.Comp where
  K := K
  Γ := fun _ => Bool
  L := Lab
  prog := prog
  ks := Finset.univ.toList
  ks_nodup := Finset.nodup_toList _
  mem_ks k := by simp

private theorem poly_convert : IsPolyTime convert :=
  Host.isPolyTime_reduction (c := comp) (cX := .inl .input) (cO := .inr true) (gX := id)
    (start := .inl .read) (done := .inr 6) (Equiv.refl Bool) convert
    (Polynomial.C 10 * (Polynomial.X + 1) + 20) rfl (fun x => by
      obtain ⟨v, S, h, he⟩ := run x
      refine ⟨v, S, ?_, ?_⟩
      · dsimp only [comp]
        rw [List.map_id, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
        have h20 : (20 : Polynomial ℕ).eval x.length = 20 := by simp
        rwa [h20]
      · change S (.inr true) = (convert x).map id
        rwa [List.map_id])

private theorem partition_reduction : PolyManyOneRed Partition.partitionDec binPackingDec :=
  ⟨convert ∘ Partition.reduceToSubsetSum,
    Partition.MembershipMachine.isPolyTime_reduceToSubsetSum.comp poly_convert, correct⟩

private theorem npHard (L : DecisionProblem) (h : L ∈ NP) : PolyManyOneRed L binPackingDec := by
  obtain ⟨f, hf, hL⟩ := Partition.partition_npComplete.2 L h
  obtain ⟨g, hg, hp⟩ := partition_reduction
  exact ⟨g ∘ f, hf.comp hg, fun x => (hL x).trans (hp (f x))⟩

end Hardness

-- Each mask selects occurrences from the current list, leaving the other occurrences for
-- later bins. Pruning empty bins bounds both the number of masks and each mask's length.
namespace Certificate

open Cslib.Complexity.Karp

private def remaining : List ℕ → List Bool → List ℕ
  | [], _ => []
  | a :: as, w =>
    if w.headD false then remaining as w.tail else a :: remaining as w.tail

private theorem selected_append_remaining (as : List ℕ) (w : List Bool) :
    (SSVerify.pick as w ++ remaining as w).Perm as := by
  induction as generalizing w with
  | nil => simp [SSVerify.pick, remaining]
  | cons a as ih =>
    cases hd : w.headD false with
    | true =>
      rw [SSVerify.pick, remaining, hd, ite_eq_left rfl, ite_eq_left rfl]
      exact (ih w.tail).cons a
    | false =>
      rw [SSVerify.pick, remaining, hd, ite_eq_right (by decide), ite_eq_right (by decide)]
      exact List.perm_middle.trans ((ih w.tail).cons a)

private theorem mask_of_sublist {s as : List ℕ} (h : s.Sublist as) :
    ∃ w : List Bool, w.length = as.length ∧ SSVerify.pick as w = s := by
  induction h with
  | slnil => exact ⟨[], rfl, rfl⟩
  | cons a _ ih =>
    obtain ⟨w, hlen, hw⟩ := ih
    exact ⟨false :: w, by simp [hlen], by simp [SSVerify.pick, hw]⟩
  | cons_cons a _ ih =>
    obtain ⟨w, hlen, hw⟩ := ih
    exact ⟨true :: w, by simp [hlen], by simp [SSVerify.pick, hw]⟩

private def valid (B : ℕ) : List (List Bool) → List ℕ → Prop
  | [], as => as = []
  | w :: ws, as => (SSVerify.pick as w).sum ≤ B ∧ valid B ws (remaining as w)

private theorem masks_sound (B : ℕ) (ws : List (List Bool)) (as : List ℕ)
    (h : valid B ws as) :
    ∃ bs : List (List ℕ), bs.length = ws.length ∧ bs.flatten.Perm as ∧
      ∀ b ∈ bs, b.sum ≤ B := by
  induction ws generalizing as with
  | nil =>
    have he : as = [] := h
    exact ⟨[], rfl, by simp [he], by simp⟩
  | cons w ws ih =>
    obtain ⟨hs, hv⟩ := h
    obtain ⟨bs, hl, hf, hc⟩ := ih _ hv
    refine ⟨SSVerify.pick as w :: bs, by simp [hl], ?_, ?_⟩
    · exact (hf.append_left _).trans (selected_append_remaining as w)
    · intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hs
      · exact hc b hb

private theorem remaining_sublist (as : List ℕ) (w : List Bool) :
    (remaining as w).Sublist as := by
  induction as generalizing w with
  | nil => exact List.Sublist.slnil
  | cons a as ih =>
    cases hd : w.headD false with
    | true =>
      rw [remaining, hd, ite_eq_left rfl]
      exact (ih w.tail).cons a
    | false =>
      rw [remaining, hd, ite_eq_right (by decide)]
      exact (ih w.tail).cons_cons a

private theorem masks_complete (B : ℕ) (bs : List (List ℕ)) (as : List ℕ)
    (hf : bs.flatten.Perm as) (hc : ∀ b ∈ bs, b.sum ≤ B) :
    ∃ ws : List (List Bool), ws.length = bs.length ∧ valid B ws as ∧
      ∀ w ∈ ws, w.length ≤ as.length := by
  induction bs generalizing as with
  | nil =>
    have he : as = [] := List.perm_nil.mp hf.symm
    exact ⟨[], rfl, he, by simp⟩
  | cons b bs ih =>
    have hflat : (b ++ bs.flatten).Perm as := hf
    obtain ⟨s, hp, hs⟩ := List.exists_perm_sublist (List.sublist_append_left b bs.flatten) hflat
    obtain ⟨w, hw, hsel⟩ := mask_of_sublist hs
    have hrem : bs.flatten.Perm (remaining as w) := by
      have h₁ := (selected_append_remaining as w).symm
      rw [hsel] at h₁
      have h₂ := hp.append_right bs.flatten
      simpa only [List.perm_append_left_iff] using (h₂.trans hflat).trans h₁
    obtain ⟨ws, hlen, hv, hbounds⟩ := ih _ hrem (fun b' hb' => hc b' (by simp [hb']))
    refine ⟨w :: ws, by simp [hlen], ⟨?_, hv⟩, ?_⟩
    · rw [hsel, hp.sum_eq]
      exact hc b (by simp)
    · intro ww hww
      rcases List.mem_cons.mp hww with rfl | hww
      · exact hw.le
      · exact (hbounds ww hww).trans (remaining_sublist as w).length_le

private theorem masks_bounded (i : BinPackingInstance) (h : BinPackingFeasible i) :
    ∃ ws : List (List Bool), ws.length ≤ i.2.2 ∧ valid i.2.1 ws i.1 ∧
      (ws.flatMap delimit).length ≤ (2 * i.1.length + 1) * i.1.length := by
  obtain ⟨bs, hK, hn, hf, hc⟩ := (short_bins i).mp h
  obtain ⟨ws, hlen, hv, hbounds⟩ := masks_complete _ _ _ hf hc
  have hframed (ws : List (List Bool)) (n : ℕ) (hw : ∀ w ∈ ws, w.length ≤ n) :
      (ws.flatMap delimit).length ≤ (2 * n + 1) * ws.length := by
    induction ws with
    | nil => simp
    | cons w ws ih =>
      have hw₁ := hw w (by simp)
      have hw₂ := ih (fun ww hww => hw ww (by simp [hww]))
      simp only [List.flatMap_cons, List.length_append, length_delimit, List.length_cons,
        Nat.mul_succ]
      omega
  exact ⟨ws, hlen.trans_le hK, hv,
    (hframed ws _ hbounds).trans (Nat.mul_le_mul_left _ (hlen.trans_le hn))⟩

end Certificate

-- The natural-number encoding is little-endian. Each more significant differing bit
-- supersedes the comparison determined by the preceding bits.
namespace Compare

open Turing TM2Program Function TM2Recursive
open Cslib.Complexity.Karp.EmitSS

private def updateFlag (allow a b : Bool) : Bool :=
  if a == b then allow else b

private def compareBits (allow : Bool) (a b : List Bool) : Bool :=
  match a, b with
  | [], [] => allow
  | x :: xs, [] => compareBits (updateFlag allow x false) xs []
  | [], y :: ys => compareBits (updateFlag allow false y) [] ys
  | x :: xs, y :: ys => compareBits (updateFlag allow x y) xs ys
termination_by a.length + b.length
decreasing_by
  all_goals simp_wf
  omega

private theorem compareBits_spec (allow : Bool) (a b : List Bool) :
    compareBits allow a b = true ↔
      bitsVal a < bitsVal b ∨ bitsVal a = bitsVal b ∧ allow = true := by
  have step (allow a b : Bool) (m n : ℕ) :
      (m < n ∨ m = n ∧ updateFlag allow a b = true) ↔
        a.toNat + 2 * m < b.toNat + 2 * n ∨
          a.toNat + 2 * m = b.toNat + 2 * n ∧ allow = true := by
    cases allow <;> cases a <;> cases b <;> simp [updateFlag] <;> omega
  cases a with
  | nil =>
    cases b with
    | nil => simp [compareBits]
    | cons y ys =>
      rw [compareBits.eq_def, compareBits_spec]
      simpa only [bitsVal_cons, bitsVal_nil, Bool.toNat_false, zero_add, mul_zero] using
        step allow false y 0 (bitsVal ys)
  | cons x xs =>
    cases b with
    | nil =>
      rw [compareBits.eq_def, compareBits_spec]
      simpa only [bitsVal_cons, bitsVal_nil, Bool.toNat_false, zero_add, mul_zero] using
        step allow x false (bitsVal xs) 0
    | cons y ys =>
      rw [compareBits.eq_def, compareBits_spec]
      simp only [bitsVal_cons]
      apply step
termination_by a.length + b.length
decreasing_by
  all_goals simp_wf
  omega

private theorem compare_nat (a b : ℕ) :
    compareBits true (Computability.encodeNat a) (Computability.encodeNat b) = true ↔
      a ≤ b := by
  rw [compareBits_spec, bitsVal_encodeNat, bitsVal_encodeNat]
  simp only [and_true]
  omega

private inductive Lab
  | test (allow : Bool)
  | done (ok : Bool)
  deriving DecidableEq, Fintype

private def st (a b : List Bool) : Bool → List Bool
  | false => a
  | true => b

private def prog : Lab → TM2.Stmt (fun _ : Bool => Bool) Lab Bool
  | .test allow =>
    .peek false (fun _ x => x.isNone) <|
    .peek true (fun empty x => empty && x.isNone) <|
    .branch id (.goto fun _ => .done allow)
      (.pop false (fun _ x => x.getD false) <|
        .pop true (fun x y => updateFlag allow x (y.getD false)) <|
        .goto Lab.test)
  | .done _ => .halt

private theorem run (a b : List Bool) (allow v : Bool) :
    ∃ w, RunLe prog (a.length + b.length + 1)
      ⟨some (.test allow), v, st a b⟩
      ⟨some (.done (compareBits allow a b)), w, st [] []⟩ := by
  cases a with
  | nil =>
    cases b with
    | nil =>
      rw [compareBits.eq_def]
      exact ⟨true, (Run.single (by simp [prog, st, TM2.stepAux])).le le_rfl⟩
    | cons y ys =>
      rw [compareBits.eq_def]
      obtain ⟨w, h⟩ := run [] ys (updateFlag allow false y) (updateFlag allow false y)
      refine ⟨w, ((Run.single ?_).le le_rfl |>.trans h).mono (by simp; omega)⟩
      change TM2.Cfg.mk _ _ _ = _
      rw [TM2.Cfg.mk.injEq]
      refine ⟨rfl, rfl, ?_⟩
      funext k
      cases k <;> rfl
  | cons x xs =>
    cases b with
    | nil =>
      rw [compareBits.eq_def]
      obtain ⟨w, h⟩ := run xs [] (updateFlag allow x false) (updateFlag allow x false)
      refine ⟨w, ((Run.single ?_).le le_rfl |>.trans h).mono (by simp; omega)⟩
      change TM2.Cfg.mk _ _ _ = _
      rw [TM2.Cfg.mk.injEq]
      refine ⟨rfl, rfl, ?_⟩
      funext k
      cases k <;> rfl
    | cons y ys =>
      rw [compareBits.eq_def]
      obtain ⟨w, h⟩ := run xs ys (updateFlag allow x y) (updateFlag allow x y)
      refine ⟨w, ((Run.single ?_).le le_rfl |>.trans h).mono (by simp; omega)⟩
      change TM2.Cfg.mk _ _ _ = _
      rw [TM2.Cfg.mk.injEq]
      refine ⟨rfl, rfl, ?_⟩
      funext k
      cases k <;> rfl
termination_by a.length + b.length
decreasing_by
  all_goals simp_wf
  omega

end Compare

-- Split an encoded list at the level of framed items without decoding the sizes.
namespace SplitMask

open Turing TM2Program
open Cslib.Complexity.Karp

private inductive K
  | items | mask | selected | rejected | ones
  deriving DecidableEq

private instance instFintypeK : Fintype K where
  elems := {K.items, .mask, .selected, .rejected, .ones}
  complete k := by cases k <;> decide

private inductive Lab
  | next | marker (selected : Bool) | payload (selected : Bool) | done
  deriving DecidableEq, Fintype

private def destination (selected : Bool) : K :=
  if selected then .selected else .rejected

private def prog : Lab → TM2.Stmt (fun _ : K => Bool) Lab Bool
  | .next =>
    .peek .items (fun _ o => o.isNone) <| .branch id (.goto fun _ => .done)
      (.pop .mask (fun _ o => o.getD false) <| .goto .marker)
  | .marker selected =>
    .pop .items (fun _ o => o.getD false) <|
      .push (destination selected) id <|
      .branch id (.goto fun _ => .payload selected)
        (if selected then .push .ones (fun _ => true) <| .goto fun _ => .next
          else .goto fun _ => .next)
  | .payload selected =>
    .pop .items (fun _ o => o.getD false) <|
      .push (destination selected) id <| .goto fun _ => .marker selected
  | .done => .halt

private def st (items mask selected rejected ones : List Bool) : K → List Bool
  | .items => items
  | .mask => mask
  | .selected => selected
  | .rejected => rejected
  | .ones => ones

private theorem block (p r m s d o : List Bool) (v take : Bool) :
    Run prog (2 * p.length + 1)
      ⟨some (.marker take), v, st (delimit p ++ r) m s d o⟩
      ⟨some .next, false, st r m
        (if take then (delimit p).reverse ++ s else s)
        (if take then d else (delimit p).reverse ++ d)
        (if take then true :: o else o)⟩ := by
  induction p generalizing s d v with
  | nil =>
    cases take <;> apply Run.single <;>
      change TM2.Cfg.mk _ _ _ = _ <;> rw [TM2.Cfg.mk.injEq] <;>
      refine ⟨rfl, rfl, ?_⟩ <;>
      funext k <;> cases k <;> rfl
  | cons b p ih =>
    have hfirst : Run prog 1
        ⟨some (.marker take), v, st (delimit (b :: p) ++ r) m s d o⟩
        ⟨some (.payload take), true, st (b :: delimit p ++ r) m
          (if take then true :: s else s) (if take then d else true :: d) o⟩ := by
      cases take <;> apply Run.single <;>
        change TM2.Cfg.mk _ _ _ = _ <;> rw [TM2.Cfg.mk.injEq] <;>
        refine ⟨rfl, rfl, ?_⟩ <;>
        funext k <;> cases k <;> rfl
    have hsecond : Run prog 1
        ⟨some (.payload take), true, st (b :: delimit p ++ r) m
          (if take then true :: s else s) (if take then d else true :: d) o⟩
        ⟨some (.marker take), b, st (delimit p ++ r) m
          (if take then b :: true :: s else s) (if take then d else b :: true :: d) o⟩ := by
      cases take <;> apply Run.single <;>
        change TM2.Cfg.mk _ _ _ = _ <;> rw [TM2.Cfg.mk.injEq] <;>
        refine ⟨rfl, rfl, ?_⟩ <;>
        funext k <;> cases k <;> rfl
    have ht := (hfirst.trans hsecond).trans (ih
      (if take then b :: true :: s else s) (if take then d else b :: true :: d) b)
    have hlen : 1 + 1 + (2 * p.length + 1) = 2 * (b :: p).length + 1 := by simp; omega
    cases take <;> simpa [delimit, List.reverse_cons, List.append_assoc] using ht.of_eq hlen

private theorem select_run (as : List ℕ) (w s d o : List Bool) (v : Bool) :
    Run prog ((bitEncode as).length + as.length + 1)
      ⟨some .next, v, st (bitEncode as) w s d o⟩
      ⟨some .done, true, st [] (w.drop as.length)
        ((bitEncode (SSVerify.pick as w)).reverse ++ s)
        ((bitEncode (Certificate.remaining as w)).reverse ++ d)
        (List.replicate (SSVerify.pick as w).length true ++ o)⟩ := by
  induction as generalizing w s d o v with
  | nil =>
    apply Run.single
    rfl
  | cons a as ih =>
    have code (a : ℕ) (as : List ℕ) : bitEncode (a :: as) =
        delimit (Computability.encodeNat a) ++ bitEncode as := by rfl'
    have first : Run prog 1 ⟨some .next, v, st (bitEncode (a :: as)) w s d o⟩
        ⟨some (.marker (w.headD false)), w.headD false, st (bitEncode (a :: as)) w.tail s d o⟩ := by
      apply Run.single
      have hn : delimit (Computability.encodeNat a) ≠ [] := by
        cases Computability.encodeNat a <;> simp [delimit]
      rw [code]
      cases w with
      | nil =>
        simp only [prog, TM2.stepAux, st, List.head?_append, Option.isNone_or, id_eq,
          List.head?_nil, Option.getD_none, List.tail_nil, cond_eq_ite, Bool.and_eq_true,
          Option.isNone_iff_eq_none, List.head?_eq_none_iff, hn, false_and, ↓reduceIte,
          List.headD_eq_head?_getD, TM2.Cfg.mk.injEq, Function.update_eq_self_iff, and_self]
      | cons b w =>
        simp only [prog, TM2.stepAux, st, List.head?_append, Option.isNone_or, id_eq,
          List.head?_cons, Option.getD_some, List.tail_cons, cond_eq_ite, Bool.and_eq_true,
          Option.isNone_iff_eq_none, List.head?_eq_none_iff, hn, false_and, ↓reduceIte,
          List.headD_eq_head?_getD, TM2.Cfg.mk.injEq, true_and]
        funext k
        cases k <;> rfl
    rw [code] at first
    have h₂ := block (Computability.encodeNat a) (bitEncode as) w.tail s d o
      (w.headD false) (w.headD false)
    have hr := (first.trans h₂).trans (ih w.tail _ _ _ false)
    rw [← code] at hr
    have hlen : 1 + (2 * (Computability.encodeNat a).length + 1) +
        ((bitEncode as).length + as.length + 1) =
          (bitEncode (a :: as)).length + (a :: as).length + 1 := by
      rw [code, List.length_append, length_delimit, List.length_cons]
      omega
    have hdrop : w.tail.drop as.length = w.drop (as.length + 1) := by
      cases w <;> simp
    rw [SSVerify.pick, Certificate.remaining]
    have he : w.head?.getD false = w.headD false := by cases w <;> rfl
    cases hw : w.headD false <;>
      (have hw' := he.trans hw
       simpa [hw, hw', code, hdrop, List.reverse_append, List.append_assoc, List.replicate_succ']
         using hr.of_eq hlen)

end SplitMask

-- Check the selected bin with the existing subset-sum accumulator and return the
-- encoded unselected items for the next iteration.
namespace CheckBin

open Turing Function TM2Program TM2Embedding
open Cslib.Complexity Cslib.Complexity.Karp Cslib.Complexity.SatVerifier
open Cslib.Complexity.PolynomialEncoding
open Computability (encodeNat)

private inductive K
  | split (k : SplitMask.K)
  | sum (k : SSVerify.K)
  | cmp (k : Bool)
  | cap | buf
  deriving DecidableEq, Fintype

@[reducible] private def Γ : K → Type
  | .sum _ => Sym
  | _ => Bool

private inductive Lab
  | split (l : SplitMask.Lab)
  | collect | restore | mask
  | sum (l : SSVerify.Lab)
  | reverse | copy1 | copy2
  | cmp (l : Compare.Lab)
  | clean (ok : Bool) | done (ok : Bool)
  deriving DecidableEq, Fintype

private def splitEmb : SEmb (fun _ : SplitMask.K => Bool) Γ :=
  ⟨K.split, fun _ _ => K.split.inj, fun _ => Equiv.refl _⟩

private def sumEmb : SEmb (fun _ : SSVerify.K => Sym) Γ :=
  ⟨K.sum, fun _ _ => K.sum.inj, fun _ => Equiv.refl _⟩

private def cmpEmb : SEmb (fun _ : Bool => Bool) Γ :=
  ⟨K.cmp, fun _ _ => K.cmp.inj, fun _ => Equiv.refl _⟩

private theorem agree_split {U : SplitMask.K → List Bool} {S : (k : K) → List (Γ k)} :
    Agree splitEmb U S ↔ ∀ k, S (.split k) = U k := by
  change (∀ k, S (.split k) = (U k).map id) ↔ _
  simp

private theorem agree_sum {U : SSVerify.K → List Sym} {S : (k : K) → List (Γ k)} :
    Agree sumEmb U S ↔ ∀ k, S (.sum k) = U k := by
  change (∀ k, S (.sum k) = (U k).map id) ↔ _
  simp

private theorem agree_cmp {U : Bool → List Bool} {S : (k : K) → List (Γ k)} :
    Agree cmpEmb U S ↔ ∀ k, S (.cmp k) = U k := by
  change (∀ k, S (.cmp k) = (U k).map id) ↔ _
  simp

private def splitLabel : SplitMask.Lab → Lab
  | .done => .collect
  | l => .split l

private def sumLabel : SSVerify.Lab → Lab
  | .yes | .no => .reverse
  | l => .sum l

private def cmpLabel : Compare.Lab → Lab
  | .done ok => .clean ok
  | l => .cmp l

private def prog : Lab → TM2.Stmt Γ Lab Bool
  | .split l => mapS splitEmb splitLabel (SplitMask.prog l)
  | .collect => moveB (.split .selected) (.sum .X) some Sym.bit .collect .restore
  | .restore => moveB (.split .rejected) (.split .items) some id .restore .mask
  | .mask => moveB (.split .ones) (.sum .W) some Sym.bit .mask (.sum .next)
  | .sum l => mapS sumEmb sumLabel (SSVerify.prog l)
  | .reverse => moveB (.sum .B) (.cmp false) Sym.bit? id .reverse .copy1
  | .copy1 => moveB .cap .buf some id .copy1 .copy2
  | .copy2 => splitB .buf .cap (.cmp true) some id id .copy2 (.cmp (.test true))
  | .cmp l => mapS cmpEmb cmpLabel (Compare.prog l)
  | .clean ok => cleanS [.split .mask, .sum .W] (.clean ok) (.done ok)
  | .done _ => .halt

private theorem embeds_split : Embeds splitEmb splitLabel SplitMask.prog prog := by
  intro l
  cases l <;> first | exact Or.inl rfl | exact Or.inr rfl

private theorem embeds_sum : Embeds sumEmb sumLabel SSVerify.prog prog := by
  intro l
  cases l <;> first | exact Or.inl rfl | exact Or.inr rfl

private theorem embeds_cmp : Embeds cmpEmb cmpLabel Compare.prog prog := by
  intro l
  cases l <;> first | exact Or.inl rfl | exact Or.inr rfl

private def st (as : List ℕ) (w : List Bool) (B : ℕ) : (k : K) → List (Γ k)
  | .split k => SplitMask.st (bitEncode as) w [] [] [] k
  | .sum _ => []
  | .cmp _ => []
  | .cap => encodeNat B
  | .buf => []

private theorem collect_run (s d : List ℕ) (w : List Bool) (B : ℕ) (v : Bool)
    (S : (k : K) → List (Γ k))
    (hs : Agree splitEmb (SplitMask.st [] w (bitEncode s).reverse (bitEncode d).reverse
      (List.replicate s.length true)) S)
    (hsum : ∀ k, S (.sum k) = [])
    (hcmp : ∀ k, S (.cmp k) = [])
    (hcap : S .cap = encodeNat B)
    (hbuf : S .buf = []) :
    ∃ v' T, Run prog ((bitEncode s).length + (bitEncode d).length + s.length + 3)
      ⟨some .collect, v, S⟩ ⟨some (.sum .next), v', T⟩ ∧
      Agree sumEmb (SSVerify.st ((bitEncode s).map .bit)
        ((List.replicate s.length true).map .bit) [] [] []) T ∧
      Agree splitEmb (SplitMask.st (bitEncode d) w [] [] []) T ∧
      (∀ k, T (.cmp k) = []) ∧ T .cap = encodeNat B ∧ T .buf = [] := by
  have hsel : S (.split .selected) = (bitEncode s).reverse := by
    simpa [SplitMask.st] using agree_split.mp hs .selected
  obtain ⟨v₁, S₁, r₁, h₁src, h₁out, h₁frame⟩ := moveB_run
    (M := prog) (self := Lab.collect) (next := Lab.restore)
    (a := K.split .selected) (b := K.sum .X) (d := some) (g := Sym.bit)
    rfl (by decide) (bitEncode s).reverse (bitEncode s).reverse [] v S
    (by simpa using hsel) (by simp [IsBitBlock, List.map_reverse]) rfl
  have hr : S₁ (.split .rejected) = (bitEncode d).reverse := by
    rw [h₁frame _ (by decide) (by decide)]
    simpa [SplitMask.st] using agree_split.mp hs .rejected
  obtain ⟨v₂, S₂, r₂, h₂src, h₂out, h₂frame⟩ := moveB_run
    (M := prog) (self := Lab.restore) (next := Lab.mask)
    (a := K.split .rejected) (b := K.split .items) (d := some) (g := id)
    rfl (by decide) (bitEncode d).reverse (bitEncode d).reverse [] v₁ S₁
    (by simpa using hr) (by simp [IsBitBlock, List.map_reverse]) rfl
  have hm : S₂ (.split .ones) = List.replicate s.length true := by
    rw [h₂frame _ (by decide) (by decide), h₁frame _ (by decide) (by decide)]
    simpa [SplitMask.st] using agree_split.mp hs .ones
  obtain ⟨v₃, S₃, r₃, h₃src, h₃out, h₃frame⟩ := moveB_run
    (M := prog) (self := Lab.mask) (next := Lab.sum .next)
    (a := K.split .ones) (b := K.sum .W) (d := some) (g := Sym.bit)
    rfl (by decide) (List.replicate s.length true) (List.replicate s.length true) [] v₂ S₂
    (by simpa using hm) (by simp [IsBitBlock, List.map_replicate]) rfl
  have hX : S₃ (.sum .X) = (bitEncode s).map Sym.bit := by
    rw [h₃frame _ (by decide) (by decide), h₂frame _ (by decide) (by decide), h₁out]
    simp [hsum, List.map_reverse]
  have hW : S₃ (.sum .W) = (List.replicate s.length true).map Sym.bit := by
    rw [h₃out, h₂frame _ (by decide) (by decide), h₁frame _ (by decide) (by decide)]
    simp [hsum, List.map_replicate]
  have hitems : S₃ (.split .items) = bitEncode d := by
    have hi : S (.split .items) = [] := by
      simpa [SplitMask.st] using agree_split.mp hs .items
    rw [h₃frame _ (by decide) (by decide), h₂out, h₁frame _ (by decide) (by decide)]
    simp [hi]
  have hmask : S₃ (.split .mask) = w := by
    rw [h₃frame _ (by decide) (by decide), h₂frame _ (by decide) (by decide),
      h₁frame _ (by decide) (by decide)]
    simpa [SplitMask.st] using agree_split.mp hs .mask
  refine ⟨v₃, S₃, ((r₁.trans r₂).trans r₃).of_eq (by simp; omega), ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    change S₃ (.sum k) = (SSVerify.st _ _ [] [] [] k).map id
    cases k with
    | X => simpa [SSVerify.st] using hX
    | W => simpa [SSVerify.st] using hW
    | T | A | B | P | Q =>
      rw [h₃frame _ (by decide) (by decide), h₂frame _ (by decide) (by decide),
        h₁frame _ (by decide) (by decide)]
      simp [hsum, SSVerify.st]
  · intro k
    change S₃ (.split k) = (SplitMask.st _ _ [] [] [] k).map id
    cases k with
    | items => simpa [SplitMask.st] using hitems
    | mask => simpa [SplitMask.st] using hmask
    | ones => simpa [SplitMask.st] using h₃src
    | selected =>
      rw [h₃frame _ (by decide) (by decide), h₂frame _ (by decide) (by decide)]
      simpa [SplitMask.st] using h₁src
    | rejected =>
      rw [h₃frame _ (by decide) (by decide)]
      simpa [SplitMask.st] using h₂src
  · intro k
    cases k <;> rw [h₃frame _ (by decide) (by decide), h₂frame _ (by decide) (by decide),
      h₁frame _ (by decide) (by decide), hcmp]
  · rw [h₃frame _ (by decide) (by decide), h₂frame _ (by decide) (by decide),
      h₁frame _ (by decide) (by decide), hcap]
  · rw [h₃frame _ (by decide) (by decide), h₂frame _ (by decide) (by decide),
      h₁frame _ (by decide) (by decide), hbuf]

private def sumTM : Turing.FinTM2 where
  K := SSVerify.K
  k₀ := .X
  k₁ := .B
  Γ := fun _ => Sym
  Λ := SSVerify.Lab
  main := .next
  σ := Bool
  initialState := false
  m := SSVerify.prog

private noncomputable def sumPushes : ℕ := TM2Composition.pushBound sumTM

private theorem sum_finish (s d : List ℕ) (w : List Bool) (B : ℕ) (v : Bool)
    (S : (k : K) → List (Γ k))
    (hS : Agree sumEmb (SSVerify.st ((bitEncode s).map .bit)
      ((List.replicate s.length true).map .bit) [] [] []) S)
    (hd : Agree splitEmb (SplitMask.st (bitEncode d) w [] [] []) S)
    (hcmp : ∀ k, S (.cmp k) = [])
    (hcap : S .cap = encodeNat B)
    (hbuf : S .buf = []) :
    let n := (bitEncode s).length
    let cap := (encodeNat B).length
    ∃ v' T, RunLe prog ((sumPushes + 1) * (n * (2 * n + 6) + n + 3) +
        (encodeNat s.sum).length * 2 + 3 * cap + s.length + w.length + 8)
      ⟨some (.sum .next), v, S⟩ ⟨some (.done (decide (s.sum ≤ B))), v', T⟩ ∧
      T = st d [] B := by
  let ones := List.replicate s.length true
  let n := (bitEncode s).length
  let bound := n * (2 * n + 6) + n + 3
  let bits := encodeNat s.sum
  have hcode : s.flatMap (fun a => delimit (encodeNat a)) = bitEncode s := by
    change _ = ((s.map encodeNat).map delimit).flatten
    simp only [List.flatMap_def, List.map_map, Function.comp_def]
  have hpick : SSVerify.pick s ones = s := SSVerifierSum.pick_all s s.length le_rfl
  obtain ⟨v₁, w₁, r₁⟩ := SSVerifierSum.sum_component_run s ones v
  rw [hcode, hpick] at r₁
  have hw₁ : w₁.length ≤ s.length + sumPushes * bound := by
    obtain ⟨m, hm, hr⟩ := r₁
    have hb := TM2Composition.length_iter sumTM SSVerify.K.W m _ _ hr
    change w₁.length ≤ (ones.map Sym.bit).length + sumPushes * m at hb
    exact (by simpa [ones] using hb : w₁.length ≤ s.length + sumPushes * m).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_left _ hm) _)
  obtain ⟨S₁, t₁, hs₁, hf₁⟩ := runLe_embed sumLabel embeds_sum r₁ hS
  have el : sumLabel (if bits = [] then SSVerify.Lab.yes else .no) = .reverse := by
    split <;> rfl
  change RunLe prog bound ⟨some (.sum .next), v, S⟩
    ⟨some (sumLabel (if bits = [] then .yes else .no)), v₁, S₁⟩ at t₁
  rw [el] at t₁
  have hs : S₁ (.sum .B) = (bits.map Sym.bit).reverse :=
    agree_sum.mp hs₁ .B
  obtain ⟨v₂, S₂, t₂, h₂src, h₂out, hf₂⟩ := moveB_run
    (M := prog) (self := Lab.reverse) (next := Lab.copy1)
    (a := K.sum .B) (b := K.cmp false) (d := Sym.bit?) (g := id) rfl (by decide)
    bits.reverse (bits.map Sym.bit).reverse [] v₁ S₁
    (by simpa using hs)
    (by simp [IsBitBlock, Sym.bit?, Function.comp_def, List.map_reverse]) rfl
  have h₂a : S₂ (.cmp false) = bits := by
    rw [h₂out, hf₁ _ (by simp [sumEmb]), hcmp]
    simp
  have h₂cap : S₂ .cap = encodeNat B := by
    rw [hf₂ _ (by decide) (by decide), hf₁ _ (by simp [sumEmb]), hcap]
  have h₂buf : S₂ .buf = [] := by
    rw [hf₂ _ (by decide) (by decide), hf₁ _ (by simp [sumEmb]), hbuf]
  obtain ⟨S₃, t₃, h₃cap, h₃buf, h₃out, hf₃⟩ := copyB_run
    (M := prog) (first := Lab.copy1) (second := Lab.copy2) (next := Lab.cmp (.test true))
    (a := K.cap) (b := K.cmp true) (t := K.buf)
    (da := some) (dt := some) (ga := id) (gb := id) (gt := id)
    rfl rfl (by decide) (by decide) (by decide) (fun _ => rfl) (fun _ => rfl)
    (encodeNat B) [] v₂ S₂ (by simpa using h₂cap) rfl (by simp [EndsBitBlock, h₂buf])
  have hcmp₃ : Agree cmpEmb (Compare.st bits (encodeNat B)) S₃ := by
    apply agree_cmp.mpr
    intro k
    cases k
    · rw [hf₃ _ (by decide) (by decide) (by decide), h₂a]
      rfl
    · rw [h₃out, hf₂ _ (by decide) (by decide), hf₁ _ (by simp [sumEmb]), hcmp]
      simp [Compare.st]
  obtain ⟨v₄, r₄⟩ := Compare.run bits (encodeNat B) true false
  obtain ⟨S₄, t₄, h₄out, hf₄⟩ := runLe_embed cmpLabel embeds_cmp r₄ hcmp₃
  have he : Compare.compareBits true bits (encodeNat B) = decide (s.sum ≤ B) := by
    rw [Bool.eq_iff_iff, decide_eq_true_eq]
    exact Compare.compare_nat s.sum B
  rw [he] at t₄
  have hsum (k : SSVerify.K) (hk : k ≠ .B) :
      S₄ (.sum k) = SSVerify.st [] w₁ [] [] (bits.map Sym.bit).reverse k := by
    rw [hf₄ _ (by simp [cmpEmb]), hf₃ _ (by simp) (by simp)
      (by simp), hf₂ _ (by simpa using hk) (by simp), agree_sum.mp hs₁]
  have hsplit (k : SplitMask.K) :
      S₄ (.split k) = SplitMask.st (bitEncode d) w [] [] [] k := by
    rw [hf₄ _ (by simp [cmpEmb]), hf₃ _ (by simp) (by simp)
      (by simp), hf₂ _ (by simp) (by simp),
      hf₁ _ (by simp [sumEmb]), agree_split.mp hd]
  let m := s.length + sumPushes * bound + w.length
  obtain t₅ := clean_run (M := prog) (ks := [K.split .mask, .sum .W])
    (self := Lab.clean (decide (s.sum ≤ B))) (next := Lab.done (decide (s.sum ≤ B)))
    rfl (by decide) m v₄ S₄ (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl
      · rw [hsplit]
        simp only [SplitMask.st, m]
        omega
      · rw [hsum _ (by decide)]
        simp only [SSVerify.st, m]
        omega)
  have hsum0 (k : SSVerify.K) (hkB : k ≠ .B) (hkW : k ≠ .W) :
      S₄ (.sum k) = [] := by
    rw [hsum k hkB]
    cases k <;> simp_all [SSVerify.st]
  have hcap₄ : S₄ .cap = encodeNat B := by
    rw [hf₄ _ (by simp [cmpEmb]), h₃cap, h₂cap]
  have hbuf₄ : S₄ .buf = [] := by
    rw [hf₄ _ (by simp [cmpEmb]), h₃buf, h₂buf]
  have hfinal : (fun k => if k ∈ [K.split .mask, .sum .W] then [] else S₄ k) =
      st d [] B := by
    funext k
    cases k with
    | split k => cases k <;> simp [hsplit, st, SplitMask.st]
    | sum k =>
      cases k with
      | W => rfl
      | B =>
        simp only [List.mem_cons, reduceCtorEq]
        rw [hf₄ _ (by simp [cmpEmb]), hf₃ _ (by decide) (by decide) (by decide), h₂src]
        rfl
      | X | T | A | P | Q =>
        simp only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq]
        apply hsum0 <;> decide
    | cmp k => cases k <;> simp [agree_cmp.mp h₄out, Compare.st, st]
    | cap => exact hcap₄
    | buf => exact hbuf₄
  rw [hfinal] at t₅
  refine ⟨false, st d [] B,
    ((((t₁.trans (t₂.le le_rfl)).trans (t₃.le le_rfl)).trans t₄).trans t₅).mono ?_, rfl⟩
  simp only [m, bound, n, bits, List.length_reverse]
  rw [Nat.add_mul, Nat.one_mul]
  omega

private theorem packing_encoding_length (as : List ℕ) :
    (bitEncode as).length =
      (as.map (fun a => (delimit (encodeNat a)).length)).sum := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    change (delimit (encodeNat a) ++ bitEncode as).length = _
    simp [ih]

private theorem bitEncode_length_split (as : List ℕ) (w : List Bool) :
    (bitEncode (SSVerify.pick as w)).length +
      (bitEncode (Certificate.remaining as w)).length = (bitEncode as).length := by
  have h := ((Certificate.selected_append_remaining as w).map
    (fun a => (delimit (encodeNat a)).length)).sum_eq
  simpa only [packing_encoding_length, List.map_append, List.sum_append] using h

private noncomputable def cost (n cap w : ℕ) : ℕ :=
  (sumPushes + 1) * (n * (2 * n + 6) + n + 3) + 7 * n + 3 * cap + w + 15

private theorem cost_mono {a a' c c' w w' : ℕ} (ha : a ≤ a') (hc : c ≤ c') (hw : w ≤ w') :
    cost a c w ≤ cost a' c' w' := by
  unfold cost
  gcongr

private theorem run (as : List ℕ) (w : List Bool) (B : ℕ) (v : Bool) :
    let s := SSVerify.pick as w
    let d := Certificate.remaining as w
    ∃ v', RunLe prog (cost (bitEncode as).length (encodeNat B).length w.length)
      ⟨some (.split .next), v, st as w B⟩
      ⟨some (.done (decide (s.sum ≤ B))), v', st d [] B⟩ := by
  let s := SSVerify.pick as w
  let d := Certificate.remaining as w
  have hz : Agree splitEmb (SplitMask.st (bitEncode as) w [] [] []) (st as w B) :=
    agree_split.mpr (fun _ => rfl)
  obtain ⟨S₁, t₁, ha₁, hf₁⟩ := run_embed splitLabel embeds_split _ _ _ _ _ _
    _ (st as w B) (SplitMask.select_run as w [] [] [] v) hz
  have hs₁ : Agree splitEmb (SplitMask.st [] (w.drop as.length) (bitEncode s).reverse
      (bitEncode d).reverse (List.replicate s.length true)) S₁ := by
    exact (by simpa [s, d] using ha₁)
  have hsum : ∀ k, S₁ (.sum k) = [] := by
    intro k
    exact hf₁ _ (by simp [splitEmb])
  have hcmp : ∀ k, S₁ (.cmp k) = [] := by
    intro k
    exact hf₁ _ (by simp [splitEmb])
  have hcap : S₁ .cap = encodeNat B := hf₁ _ (by simp [splitEmb])
  have hbuf : S₁ .buf = [] := hf₁ _ (by simp [splitEmb])
  obtain ⟨v₂, S₂, t₂, hs₂, hd₂, hc₂, hb₂, ht₂⟩ :=
    collect_run s d (w.drop as.length) B true S₁ hs₁ hsum hcmp hcap hbuf
  obtain ⟨v₃, S₃, t₃, hS₃⟩ := sum_finish s d (w.drop as.length) B v₂ S₂
    hs₂ hd₂ hc₂ hb₂ ht₂
  rw [hS₃] at t₃
  refine ⟨v₃, (((t₁.trans t₂).le le_rfl).trans t₃).mono ?_⟩
  have hsum := Partition.sum_encoding_length_le s
  have hsplit := bitEncode_length_split as w
  have hs : (bitEncode s).length ≤ (bitEncode as).length := by
    change (bitEncode s).length + (bitEncode d).length = _ at hsplit
    omega
  have hlen (xs : List ℕ) : xs.length ≤ (bitEncode xs).length := by
    have h := length_le_length_flatten_delimit (xs.map encodeNat)
    rwa [List.length_map] at h
  have hdrop : (w.drop as.length).length ≤ w.length := by
    rw [List.length_drop]
    omega
  have hpoly : (sumPushes + 1) * ((bitEncode s).length * (2 * (bitEncode s).length + 6) +
        (bitEncode s).length + 3) ≤
      (sumPushes + 1) * ((bitEncode as).length * (2 * (bitEncode as).length + 6) +
        (bitEncode as).length + 3) := by gcongr
  have hsCount := hlen s
  have hTotalCount := hlen as
  change (bitEncode s).length + (bitEncode d).length = (bitEncode as).length at hsplit
  dsimp only [cost]
  omega

end CheckBin

-- Process the framed masks in sequence. Count completed masks in unary, then compare
-- their binary count with the input limit once the witness is exhausted.
namespace Verify

open Turing Function TM2Program TM2Embedding
open Cslib.Complexity Cslib.Complexity.Karp Cslib.Complexity.SatVerifier
open Cslib.Complexity.PolynomialEncoding
open Computability (encodeNat)

private def accepts (B limit used : ℕ) (as : List ℕ) (w : List Bool) : Prop :=
  ∃ masks : List (List Bool), masks.flatMap delimit = w ∧
    masks.length + used ≤ limit ∧ Certificate.valid B masks as

private theorem accepts_nil (B limit used : ℕ) (as : List ℕ) :
    accepts B limit used as [] ↔ as = [] ∧ used ≤ limit := by
  constructor
  · rintro ⟨masks, he, hn, hv⟩
    cases masks with
    | nil => exact ⟨hv, by simpa using hn⟩
    | cons m masks =>
      have := List.length_eq_zero_iff.mpr he
      simp only [List.flatMap_cons, List.length_append, length_delimit] at this
      omega
  · rintro ⟨rfl, hu⟩
    exact ⟨[], rfl, by simpa using hu, rfl⟩

private theorem accepts_bad (B limit used : ℕ) (as : List ℕ)
    {w : List Bool} (hn : w ≠ []) (hb : undelimit w = none) :
    ¬ accepts B limit used as w := by
  rintro ⟨masks, rfl, -⟩
  cases masks with
  | nil => exact hn rfl
  | cons m masks => simp only [List.flatMap_cons, undelimit_delimit, reduceCtorEq] at hb

private theorem accepts_step (B limit used : ℕ) (as : List ℕ) (m w : List Bool) :
    accepts B limit used as (delimit m ++ w) ↔
      (SSVerify.pick as m).sum ≤ B ∧
        accepts B limit (used + 1) (Certificate.remaining as m) w := by
  constructor
  · rintro ⟨masks, he, hk, hv⟩
    cases masks with
    | nil =>
      have := congrArg (undelimit) he
      simp only [List.flatMap_nil, undelimit, undelimit_delimit, reduceCtorEq] at this
    | cons hd tl =>
      have h := congrArg undelimit he
      simp only [List.flatMap_cons, undelimit_delimit, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, htail⟩ := h
      exact ⟨hv.1, tl, htail, by simp only [List.length_cons] at hk; omega, hv.2⟩
  · rintro ⟨hB, tl, htail, hlim, hv⟩
    refine ⟨m :: tl, by simp [htail], ?_, ⟨hB, hv⟩⟩
    simp only [List.length_cons]
    omega

private inductive K
  | core (k : CheckBin.K)
  | count (k : EmitSS.K)
  | witness | buf | limit
  deriving DecidableEq, Fintype

@[reducible] private def Γ : K → Type
  | .core k => CheckBin.Γ k
  | .count k => EmitSS.Γ k
  | _ => Bool

private inductive Lab
  | loop | read | back
  | core (l : CheckBin.Lab)
  | tick
  | count (l : UnaryNat.Lab)
  | cmp (l : Compare.Lab)
  | accept | reject
  deriving DecidableEq, Fintype

private def coreEmb : SEmb CheckBin.Γ Γ :=
  ⟨K.core, fun _ _ => K.core.inj, fun _ => Equiv.refl _⟩

private def countEmb : SEmb EmitSS.Γ Γ :=
  ⟨K.count, fun _ _ => K.count.inj, fun _ => Equiv.refl _⟩

private def cmpEmb : SEmb (fun _ : Bool => Bool) Γ where
  e | false => .count .O | true => .limit
  inj a b h := by cases a <;> cases b <;> simp_all
  ι | false => Equiv.refl Bool | true => Equiv.refl Bool

private def coreLabel : CheckBin.Lab → Lab
  | .done true => .tick
  | .done false => .reject
  | l => .core l

private def countLabel : UnaryNat.Lab → Lab
  | .done => .cmp (.test true)
  | l => .count l

private def cmpLabel : Compare.Lab → Lab
  | .done true => .accept
  | .done false => .reject
  | l => .cmp l

private def prog : Lab → TM2.Stmt Γ Lab Bool
  | .loop =>
    .peek .witness (fun _ o => o.isNone) <| .branch id
      (.peek (.core (.split .items)) (fun _ o => o.isNone) <|
        .branch id (.goto fun _ => .count (.emit .hv)) (.goto fun _ => .reject))
      (.goto fun _ => .read)
  | .read => FramedCNF.Block.read .witness .buf some id .read .back .reject
  | .back => moveB .buf (.core (.split .mask)) some id .back (.core (.split .next))
  | .core l => mapS coreEmb coreLabel (CheckBin.prog l)
  | .tick => .push (.count .A) (fun _ => EmitSS.U) <| .goto fun _ => .loop
  | .count l => mapS countEmb countLabel (UnaryNat.prog false l)
  | .cmp l => mapS cmpEmb cmpLabel (Compare.prog l)
  | .accept | .reject => .halt

private theorem embeds_core : Embeds coreEmb coreLabel CheckBin.prog prog := by
  intro l
  cases l
  case done ok => cases ok <;> exact Or.inr rfl
  all_goals exact Or.inl rfl

private theorem embeds_count : Embeds countEmb countLabel (UnaryNat.prog false) prog := by
  intro l
  cases l <;> first | exact Or.inl rfl | exact Or.inr rfl

private theorem embeds_cmp : Embeds cmpEmb cmpLabel Compare.prog prog := by
  intro l
  cases l with
  | test _ => exact Or.inl rfl
  | done ok => cases ok <;> exact Or.inr rfl

private def countSt (n : ℕ) : (k : EmitSS.K) → List (EmitSS.Γ k)
  | .A => cnt EmitSS.U n
  | _ => []

private def st (as : List ℕ) (B limit used : ℕ) (w mask buf : List Bool) :
    (k : K) → List (Γ k)
  | .core k => CheckBin.st as mask B k
  | .count k => countSt used k
  | .witness => w
  | .buf => buf
  | .limit => encodeNat limit

private theorem count_run (as : List ℕ) (B limit used : ℕ) (v : Bool) :
    ∃ w T, RunLe prog (711 * used + (encodeNat limit).length + 307)
      ⟨some (.count (.emit .hv)), v, st as B limit used [] [] []⟩
      ⟨some (if used ≤ limit then .accept else .reject), w, T⟩ := by
  obtain ⟨v₁, U, r₁, hO, -⟩ := UnaryNat.run_raw used [] v (countSt used)
    rfl rfl rfl rfl rfl
  have hS : Agree countEmb (countSt used) (st as B limit used [] [] []) := by
    intro k
    change countSt used k = (countSt used k).map id
    simp
  obtain ⟨S, t₁, h₁, hf₁⟩ := runLe_embed countLabel embeds_count r₁ hS
  obtain ⟨v₂, r₂⟩ := Compare.run (encodeNat used) (encodeNat limit) true v₁
  have hcmp : Agree cmpEmb (Compare.st (encodeNat used) (encodeNat limit)) S := by
    intro k
    cases k
    · have h := h₁ EmitSS.K.O
      change S (.count .O) = (U .O).map id at h
      change S (.count .O) = (encodeNat used).map id
      simpa [hO] using h
    · have h := hf₁ K.limit (by simp [countEmb])
      change S .limit = (encodeNat limit).map id
      simpa [st] using h
  obtain ⟨T, t₂, -⟩ := runLe_embed cmpLabel embeds_cmp r₂ hcmp
  have he : cmpLabel (.done (Compare.compareBits true (encodeNat used) (encodeNat limit))) =
      (if used ≤ limit then .accept else .reject) := by
    cases h : Compare.compareBits true (encodeNat used) (encodeNat limit)
    · have h' : ¬ used ≤ limit := by
        intro hle
        have := (Compare.compare_nat used limit).mpr hle
        simp [h] at this
      simp [h', cmpLabel]
    · have := (Compare.compare_nat used limit).mp h
      simp [this, cmpLabel]
  rw [he] at t₂
  refine ⟨v₂, T, (t₁.trans t₂).mono ?_⟩
  have hl := EmitSS.encodeNat_length_le used
  omega

private theorem read_run (as : List ℕ) (m r : List Bool) (B limit used : ℕ) (v : Bool) :
    ∃ v', Run prog (2 * m.length + 2)
      ⟨some .read, v, st as B limit used (delimit m ++ r) [] []⟩
      ⟨some (.core (.split .next)), v', st as B limit used r m []⟩ := by
  obtain ⟨S, t₁, hW, hB, hf⟩ := FramedCNF.Block.run_delimit
    (M := prog) (a := K.witness) (b := K.buf) (d := some) (g := id)
    (self := Lab.read) (good := Lab.back) (bad := Lab.reject)
    rfl (by decide) id (fun _ => rfl) m r v
    (st as B limit used (delimit m ++ r) [] []) (by simp [st])
  have hS : S = st as B limit used r [] m.reverse := by
    funext k
    cases k
    case witness => exact hW
    case buf => simpa [st] using hB
    all_goals exact hf _ (by simp) (by simp)
  rw [hS] at t₁
  obtain ⟨v₂, T, t₂, hbuf, hmask, hf₂⟩ := moveB_run
    (M := prog) (a := K.buf) (b := K.core (.split .mask))
    (d := some) (g := id) (self := Lab.back) (next := Lab.core (.split .next))
    rfl (by decide) m.reverse m.reverse [] false (st as B limit used r [] m.reverse)
    (by simp [st]) (by simp [IsBitBlock]) rfl
  have hT : T = st as B limit used r m [] := by
    funext k
    cases k with
    | buf => exact hbuf
    | core k =>
      cases k with
      | split sk =>
        cases sk with
        | mask => simpa [st, CheckBin.st, SplitMask.st] using hmask
        | items | selected | rejected | ones => exact hf₂ _ (by decide) (by decide)
      | sum k | cmp k | cap | buf => exact hf₂ _ (by simp) (by simp)
    | count k | limit | witness => exact hf₂ _ (by simp) (by simp)
  rw [hT] at t₂
  exact ⟨v₂, (t₁.trans t₂).of_eq (by simp; omega)⟩

private theorem bin_run (as : List ℕ) (m w : List Bool) (B limit used : ℕ) (v : Bool) :
    let d := Certificate.remaining as m
    ∃ v', RunLe prog (CheckBin.cost (bitEncode as).length (encodeNat B).length m.length)
      ⟨some (.core (.split .next)), v, st as B limit used w m []⟩
      ⟨some (if (SSVerify.pick as m).sum ≤ B then .tick else .reject),
        v', st d B limit used w [] []⟩ := by
  let d := Certificate.remaining as m
  have ha : Agree coreEmb (CheckBin.st as m B) (st as B limit used w m []) := by
    intro k
    change CheckBin.st as m B k = (CheckBin.st as m B k).map id
    simp
  obtain ⟨u, r⟩ := CheckBin.run as m B v
  obtain ⟨T, h, ho, hf⟩ := runLe_embed coreLabel embeds_core r ha
  have he : coreLabel (.done (decide ((SSVerify.pick as m).sum ≤ B))) =
      if (SSVerify.pick as m).sum ≤ B then .tick else .reject := by
    by_cases hh : (SSVerify.pick as m).sum ≤ B <;> simp [hh, coreLabel]
  have hout : T = st d B limit used w [] [] := by
    funext k
    cases k
    case core k =>
      have hkk := ho k
      change T (.core k) = (CheckBin.st d [] B k).map id at hkk
      simpa [st] using hkk
    all_goals exact hf _ (by simp [coreEmb])
  rw [he, hout] at h
  exact ⟨u, h⟩

private theorem code_empty_iff (as : List ℕ) : bitEncode as = [] ↔ as = [] := by
  have hlen := length_le_length_flatten_delimit (as.map encodeNat)
  change (as.map encodeNat).length ≤ (bitEncode as).length at hlen
  constructor
  · intro h
    rw [List.length_map, h, List.length_nil] at hlen
    exact List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hlen)
  · rintro rfl
    rfl

private noncomputable def stepCost (N : ℕ) : ℕ :=
  CheckBin.cost N N N + 1000 * (N + 1) + 10

-- The arithmetic solver needs extra recursion depth for the machine-cost coefficients.
set_option maxRecDepth 4096 in
private theorem count_bound {used n size budget : ℕ} (hu : used ≤ n) (hs : size ≤ n)
    (hb : 1000 * (n + 1) + 10 ≤ budget) : 1 + (711 * used + size + 307) ≤ budget := by
  omega

open Classical in
private theorem loop_run (N : ℕ) (B limit used : ℕ) (as : List ℕ)
    (w : List Bool) (v : Bool)
    (has : (bitEncode as).length ≤ N) (hcap : (encodeNat B).length ≤ N)
    (hlimit : (encodeNat limit).length ≤ N) (hw : used + w.length ≤ N) :
    ∃ u T, RunLe prog ((w.length + 1) * stepCost N)
      ⟨some .loop, v, st as B limit used w [] []⟩
      ⟨some (if accepts B limit used as w then .accept else .reject), u, T⟩ := by
  classical
  have hD : 1000 * (N + 1) + 10 ≤ stepCost N := by unfold stepCost; omega
  have hleD : stepCost N ≤ (w.length + 1) * stepCost N :=
    Nat.le_mul_of_pos_left _ (by omega)
  by_cases h0 : w = []
  · subst w
    rw [accepts_nil]
    by_cases he : as = []
    · have t₀ : Run prog 1 ⟨some .loop, v, st as B limit used [] [] []⟩
          ⟨some (.count (.emit .hv)), true, st as B limit used [] [] []⟩ := by
        apply Run.single
        have hn : bitEncode ([] : List ℕ) = [] := rfl
        simp [he, prog, st, CheckBin.st, SplitMask.st, TM2.stepAux, hn]
      obtain ⟨u, T, t₁⟩ := count_run as B limit used true
      refine ⟨u, T, ?_⟩
      have hu : used ≤ N := by simpa using hw
      simpa [he] using ((t₀.le le_rfl).trans t₁).mono (count_bound hu hlimit hD)
    · have t₀ : Run prog 1 ⟨some .loop, v, st as B limit used [] [] []⟩
          ⟨some .reject, false, st as B limit used [] [] []⟩ := by
        apply Run.single
        simp [he, code_empty_iff, prog, st, CheckBin.st, SplitMask.st, TM2.stepAux]
      exact ⟨false, _, by simpa [he] using t₀.le (show 1 ≤ stepCost N by omega)⟩
  · have t₀ : Run prog 1 ⟨some .loop, v, st as B limit used w [] []⟩
        ⟨some .read, false, st as B limit used w [] []⟩ := by
      apply Run.single
      simp [h0, prog, st, TM2.stepAux]
    cases hd : undelimit w with
    | none =>
      have hno := accepts_bad B limit used as h0 hd
      obtain ⟨u, T, t₁⟩ := FramedCNF.Block.run_none
        (M := prog) (a := K.witness) (b := K.buf) (d := some) (g := id)
        (self := Lab.read) (good := Lab.back) (bad := Lab.reject)
        rfl (by decide) id (fun _ => rfl) w false (st as B limit used w [] [])
        (by simp [st]) hd
      refine ⟨u, T, ?_⟩
      simpa [hno] using ((t₀.le le_rfl).trans t₁).mono
        (show 1 + (w.length + 1) ≤ (w.length + 1) * stepCost N by omega)
    | some mr =>
      obtain ⟨m, r⟩ := mr
      have e := (Cslib.CookLevin.undelimit_eq_some_iff _ _ _).mp hd
      have hl : w.length = 2 * m.length + 1 + r.length := by
        rw [e, List.length_append, length_delimit]
      have hm : m.length ≤ N := by omega
      obtain ⟨v₁, t₁⟩ := read_run as m r B limit used false
      rw [← e] at t₁
      obtain ⟨v₂, t₂⟩ := bin_run as m r B limit used v₁
      have hv := CheckBin.cost_mono has hcap hm
      have hb : 1 + (2 * m.length + 2) +
          CheckBin.cost (bitEncode as).length (encodeNat B).length m.length + 1 ≤
          stepCost N := by
        unfold stepCost
        omega
      have h_iff : accepts B limit used as w ↔
          (SSVerify.pick as m).sum ≤ B ∧ accepts B limit (used + 1)
            (Certificate.remaining as m) r := by rw [e]; exact accepts_step B limit used as m r
      by_cases hi : (SSVerify.pick as m).sum ≤ B
      · rw [ite_eq_left hi] at t₂
        have t₃ : Run prog 1
            ⟨some .tick, v₂, st (Certificate.remaining as m) B limit used r [] []⟩
            ⟨some .loop, v₂, st (Certificate.remaining as m) B limit (used + 1) r [] []⟩ := by
          apply Run.single
          simp only [prog, TM2.stepAux, st, countSt, TM2.Cfg.mk.injEq, true_and]
          funext k
          cases k with
          | count k => cases k <;> simp [st, countSt, cnt_succ]
          | core _ | limit | witness | buf => rfl
        have has' : (bitEncode (Certificate.remaining as m)).length ≤ N := by
          have h := CheckBin.bitEncode_length_split as m
          omega
        obtain ⟨u, T, t₄⟩ := loop_run N B limit (used + 1) (Certificate.remaining as m)
          r v₂ has' hcap hlimit (by omega)
        refine ⟨u, T, ?_⟩
        rw [h_iff]
        simp only [hi, true_and]
        refine ((((t₀.trans t₁).le le_rfl |>.trans t₂).trans (t₃.le le_rfl)).trans t₄).mono ?_
        calc
          _ ≤ stepCost N + (r.length + 1) * stepCost N := Nat.add_le_add_right hb _
          _ = (r.length + 2) * stepCost N := by
            change _ = ((r.length + 1) + 1) * stepCost N
            conv_rhs => rw [Nat.add_mul, Nat.one_mul]
            exact Nat.add_comm _ _
          _ ≤ (w.length + 1) * stepCost N := Nat.mul_le_mul_right _ (by omega)
      · rw [ite_eq_right hi] at t₂
        refine ⟨v₂, st (Certificate.remaining as m) B limit used r [] [], ?_⟩
        rw [h_iff]
        simpa [hi] using (((t₀.trans t₁).le le_rfl).trans t₂).mono
          (show 1 + (2 * m.length + 2) +
              CheckBin.cost (bitEncode as).length (encodeNat B).length m.length ≤
              (w.length + 1) * stepCost N by omega)
termination_by w.length
decreasing_by omega

end Verify

-- Normalize the three instance fields on raw input before entering the verifier loop.
namespace Machine

open Turing Function TM2Program TM2Embedding ComplexityTheory
open Cslib.Complexity Cslib.Complexity.Karp Cslib.Complexity.PolynomialEncoding
open Computability (encodeNat)

open Classical in
private noncomputable def check (x w : List Bool) : Bool :=
  match bitDecode (α := BinPackingInstance) x with
  | none => false
  | some (as, B, K) => decide (Verify.accepts B K 0 as w)

private inductive K
  | list (k : ListNatMachine.K)
  | pair (k : NatPair.K)
  | ver (k : Verify.K)
  | scratch
  deriving DecidableEq, Fintype

@[reducible] private def Γ : K → Type
  | .ver k => Verify.Γ k
  | _ => Bool

private inductive Lab
  | outer (l : PairSplit.Lab)
  | list (l : ListNatMachine.Lab)
  | pair (l : NatPair.Lab)
  | ver (l : Verify.Lab)
  | yes | no
  deriving DecidableEq, Fintype

private abbrev input : K := .pair (.pair .input)
private abbrev wit : K := .ver .witness
private abbrev items : K := .ver (.core (.split .items))
private abbrev cap : K := .ver (.core .cap)
private abbrev limit : K := .ver .limit

private def outerEmb : SEmb (fun _ : PairSplit.K => Bool) Γ where
  e | .input => input | .left => .list .input | .scratch => .scratch
  inj a b h := by cases a <;> cases b <;> simp_all
  ι | .input | .left | .scratch => Equiv.refl Bool

private def listEmb : SEmb (fun _ : ListNatMachine.K => Bool) Γ where
  e | .output => items | k => .list k
  inj a b h := by cases a <;> cases b <;> simp_all
  ι | .input | .output | .acc | .nat _ => Equiv.refl Bool

private def pairEmb : SEmb (fun _ : NatPair.K => Bool) Γ where
  e | .left => cap | .right => limit | k => .pair k
  inj a b h := by cases a <;> cases b <;> simp_all
  ι | .left | .right | .pair _ | .buffer => Equiv.refl Bool

private def verEmb : SEmb Verify.Γ Γ :=
  ⟨K.ver, fun _ _ => K.ver.inj, fun _ => Equiv.refl _⟩

private def outerLabel : PairSplit.Lab → Lab
  | .good => .list .loop
  | .bad => .no
  | l => .outer l

private def listLabel : ListNatMachine.Lab → Lab
  | .good => .pair (.pair .read)
  | .bad => .no
  | l => .list l

private def pairLabel : NatPair.Lab → Lab
  | .good => .ver .loop
  | .bad => .no
  | l => .pair l

private def verLabel : Verify.Lab → Lab
  | .accept => .yes
  | .reject => .no
  | l => .ver l

private def prog : Lab → TM2.Stmt Γ Lab Bool
  | .outer l => mapS outerEmb outerLabel (PairSplit.prog l)
  | .list l => mapS listEmb listLabel (ListNatMachine.prog l)
  | .pair l => mapS pairEmb pairLabel (NatPair.prog l)
  | .ver l => mapS verEmb verLabel (Verify.prog l)
  | .yes | .no => .halt

private theorem embeds_outer : Embeds outerEmb outerLabel PairSplit.prog prog := by
  intro l
  cases l <;> first | exact Or.inl rfl | exact Or.inr rfl

private theorem embeds_list : Embeds listEmb listLabel ListNatMachine.prog prog := by
  intro l
  cases l <;> first | exact Or.inl rfl | exact Or.inr rfl

private theorem embeds_pair : Embeds pairEmb pairLabel NatPair.prog prog := by
  intro l
  cases l <;> first | exact Or.inl rfl | exact Or.inr rfl

private theorem embeds_ver : Embeds verEmb verLabel Verify.prog prog := by
  intro l
  cases l <;> exact Or.inl rfl

private def args (p r w : List Bool) : (k : K) → List (Γ k) :=
  update (update (update (fun _ => []) input r) (.list .input) p) wit w

private def init (x w : List Bool) : (k : K) → List (Γ k) :=
  update (update (fun _ => []) input x) wit w

private theorem after_outer {S : (k : K) → List (Γ k)} {x p r w : List Bool}
    (h : Agree outerEmb (PairSplit.st r p []) S)
    (hf : Frame outerEmb (init x w) S) : S = args p r w := by
  have hi := h .input
  have hl := h .left
  have hs := h .scratch
  change S input = (r.map id) at hi
  change S (.list .input) = (p.map id) at hl
  change S .scratch = [] at hs
  funext k
  cases k with
  | scratch => simpa [args] using hs
  | ver k =>
    rw [hf _ (by intro q; cases q <;> simp [outerEmb])]
    cases k <;> simp [args, init]
  | list k =>
    cases k with
    | input => simpa [args] using hl
    | output | acc | nat _ =>
      rw [hf _ (by intro q; cases q <;> simp [outerEmb])]
      simp [args, init]
  | pair k =>
    cases k with
    | pair k =>
      cases k with
      | input => simpa [args] using hi
      | left | scratch =>
        rw [hf _ (by intro q; cases q <;> simp [outerEmb])]
        simp [args, init]
    | left | right | buffer =>
      rw [hf _ (by intro q; cases q <;> simp [outerEmb])]
      simp [args, init]

private theorem decode_fields (x : List Bool) :
    bitDecode (α := BinPackingInstance) x =
      match undelimit x with
      | none => none
      | some (p, r) =>
        match bitDecode (α := List ℕ) p, bitDecode (α := ℕ × ℕ) r with
        | some as, some bk => some (as, bk)
        | _, _ => none := by
  rfl'

private noncomputable def time (N : ℕ) : ℕ :=
  (N + 1) * Verify.stepCost N + 15 * N + 15

open Classical in
private theorem run (x w : List Bool) :
    ∃ u T, RunLe prog (time (3 * (x.length + w.length)))
      ⟨some (.outer .read), false, init x w⟩
      ⟨some (if check x w then .yes else .no), u, T⟩ := by
  let N := 3 * (x.length + w.length)
  have hinit : Agree outerEmb (PairSplit.st x [] []) (init x w) := by
    intro k
    cases k with
    | input =>
      change x = x.map id
      simp
    | left | scratch => simp [outerEmb, PairSplit.st, init]
  obtain ⟨v₁, S₁, t₁, hf₁, ha₁⟩ :=
    PairSplit.run_embedded outerEmb outerLabel embeds_outer x false (init x w) hinit
  have hprep : 15 * x.length + 15 ≤ time N := by
    unfold time N
    omega
  cases hx : undelimit x with
  | none =>
    simp only [hx, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, outerLabel] at t₁
    refine ⟨v₁, S₁, ?_⟩
    rw [check, decode_fields, hx]
    exact t₁.mono ((show x.length + 1 ≤ 15 * x.length + 15 by omega).trans hprep)
  | some pr =>
    obtain ⟨p, r⟩ := pr
    have xe := (Cslib.CookLevin.undelimit_eq_some_iff _ _ _).mp hx
    have xl : x.length = 2 * p.length + 1 + r.length := by
      rw [xe, List.length_append, length_delimit]
    have he₁ := after_outer (ha₁ p r hx) hf₁
    simp only [hx, Option.isSome_some, ↓reduceIte, he₁, outerLabel] at t₁
    have hin₂ : Agree listEmb (ListNatMachine.st p [] []
        (FramedCNF.NormalizeMachine.st [] [] [])) (args p r w) := by
      intro k
      cases k with
      | nat k => cases k <;>
          simp [listEmb, ListNatMachine.st, FramedCNF.NormalizeMachine.st, args]
      | input =>
        change p = p.map id
        simp
      | acc | output => simp [listEmb, ListNatMachine.st, args]
    obtain ⟨v₂, S₂, t₂, hf₂, ha₂⟩ :=
      ListNatMachine.run_embedded listEmb listLabel embeds_list p v₁ (args p r w) hin₂
    cases hp : bitDecode (α := List ℕ) p with
    | none =>
      simp only [hp, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, listLabel] at t₂
      refine ⟨v₂, S₂, ?_⟩
      simp only [check, decode_fields, hx, hp]
      exact (t₁.trans t₂).mono ((show x.length + 1 + (11 * p.length + 2) ≤
        15 * x.length + 15 by omega).trans hprep)
    | some as =>
      simp only [hp, Option.isSome_some, ↓reduceIte, listLabel] at t₂
      have hin₃ : Agree pairEmb (NatPair.st r [] [] [] [] []) S₂ := by
        intro k
        have hf (k : NatPair.K) : S₂ (pairEmb.e k) = args p r w (pairEmb.e k) := by
          apply hf₂
          intro q
          cases k <;> cases q <;> simp [listEmb, pairEmb]
        rw [hf k]
        cases k with
        | pair k =>
          cases k with
          | input =>
            change r = r.map id
            simp
          | left | scratch => simp [pairEmb, NatPair.st, args]
        | left | right | buffer => simp [pairEmb, NatPair.st, args]
      obtain ⟨v₃, S₃, t₃, hf₃, ha₃⟩ :=
        NatPair.run_embedded pairEmb pairLabel embeds_pair r v₂ S₂ hin₃
      have h123 : x.length + 1 + (11 * p.length + 2) + (2 * r.length + 6) ≤
          15 * x.length + 15 := by omega
      cases hr : bitDecode (α := ℕ × ℕ) r with
      | none =>
        simp only [hr, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, pairLabel] at t₃
        refine ⟨v₃, S₃, ?_⟩
        simp only [check, decode_fields, hx, hp, hr]
        exact ((t₁.trans t₂).trans t₃).mono (h123.trans hprep)
      | some bk =>
        obtain ⟨B, k⟩ := bk
        simp only [hr, Option.isSome_some, ↓reduceIte, pairLabel] at t₃
        have hitems₂ := ha₂ as hp ListNatMachine.K.output
        have hcap₃ := ha₃ B k hr NatPair.K.left
        have hlimit₃ := ha₃ B k hr NatPair.K.right
        change S₂ items = (bitEncode as).map id at hitems₂
        change S₃ cap = (encodeNat B).map id at hcap₃
        change S₃ limit = (encodeNat k).map id at hlimit₃
        have hitems₃ : S₃ items = bitEncode as := by
          rw [hf₃ _ (by intro q; cases q <;> simp [pairEmb]), hitems₂]
          exact List.map_id _
        have hframe (j : Verify.K) (hI : K.ver j ≠ items) (hC : K.ver j ≠ cap)
            (hL : K.ver j ≠ limit) : S₃ (.ver j) = args p r w (.ver j) := by
          rw [hf₃ _ (by intro q; cases q <;> simp [pairEmb, Ne.symm hC, Ne.symm hL]),
            hf₂ _ (by intro q; cases q <;> simp [listEmb, Ne.symm hI])]
        have hvinit : Agree verEmb (Verify.st as B k 0 w [] []) S₃ := by
          intro j
          change S₃ (.ver j) = (Verify.st as B k 0 w [] [] j).map id
          rw [List.map_id]
          cases j with
          | witness => rw [hframe _ (by decide) (by decide) (by decide)]; simp [args, Verify.st]
          | limit => simpa [Verify.st] using hlimit₃
          | buf => rw [hframe _ (by decide) (by decide) (by decide)]; simp [args, Verify.st]
          | count c =>
            rw [hframe _ (by simp) (by simp) (by simp)]
            cases c <;> rfl
          | core c =>
            cases c with
            | cap => simpa [Verify.st, CheckBin.st] using hcap₃
            | split c =>
              cases c with
              | items => exact hitems₃
              | mask | selected | rejected | ones =>
                rw [hframe _ (by decide) (by decide) (by decide)]
                rfl
            | buf | sum _ | cmp _ =>
              rw [hframe _ (by simp) (by simp) (by simp)]
              rfl
        have hls := decoded_list_nat_encode_length_le hp
        have hlk := NatPair.decoded_payload_length_le hr
        have hpN : 3 * p.length ≤ N := by dsimp only [N]; omega
        have hrN : r.length + 1 ≤ N := by dsimp only [N]; omega
        obtain ⟨u, U, t₄⟩ := Verify.loop_run N B k 0 as w v₃
          (hls.trans hpN) (by omega) (by omega) (by dsimp only [N]; omega)
        obtain ⟨T, t₅, -⟩ := runLe_embed verLabel embeds_ver t₄ hvinit
        have hend : verLabel (if Verify.accepts B k 0 as w then .accept else .reject) =
            if check x w then .yes else .no := by
          classical
          simp only [check, decode_fields, hx, hp, hr]
          by_cases h : Verify.accepts B k 0 as w <;> simp [h, verLabel]
        rw [hend] at t₅
        refine ⟨u, T, (((t₁.trans t₂).trans t₃).trans t₅).mono ?_⟩
        have hW : (w.length + 1) * Verify.stepCost N ≤ (N + 1) * Verify.stepCost N :=
          Nat.mul_le_mul_right _ (by dsimp only [N]; omega)
        unfold time
        dsimp only [N] at *
        omega

private noncomputable def component : Host.Comp where
  K := K
  Γ := Γ
  finΓ k := by
    cases k with
    | ver k =>
      cases k with
      | core c => cases c <;> infer_instance
      | count c => exact (UnaryNat.component false).finΓ c
      | witness | buf | limit => infer_instance
    | list _ | pair _ | scratch => infer_instance
  L := Lab
  prog := prog
  ks := Finset.univ.toList
  ks_nodup := Finset.nodup_toList _
  mem_ks k := by simp

private noncomputable def timePoly : Polynomial ℕ :=
  let C := Polynomial.C (R := ℕ)
  let X := C 3 * Polynomial.X
  let step := C (CheckBin.sumPushes + 1) * (X * (C 2 * X + C 6) + X + C 3) +
    C 7 * X + C 3 * X + X + C 15 + C 1000 * (X + C 1) + C 10
  (X + C 1) * step + C 15 * X + C 15

private theorem timePoly_eval (N : ℕ) : timePoly.eval N = time (3 * N) := by
  simp [timePoly, time, Verify.stepCost, CheckBin.cost]

private theorem check_poly : IsPolyTime (fun q : List Bool × List Bool => check q.1 q.2) :=
  Host.isPolyTime_verifier (c := component) (cX := input) (cW := wit) (gX := id) (gW := id)
    (start := .outer .read) (yes := .yes) (no := .no) check timePoly
    (by intro h; cases h) (by intro h; cases h) rfl rfl (by
      intro x w
      obtain ⟨u, T, h⟩ := run x w
      refine ⟨u, T, ?_⟩
      rw [timePoly_eval]
      dsimp only [component]
      rw [List.map_id, List.map_id]
      exact h)

private noncomputable def witnessPoly : Polynomial ℕ :=
  (Polynomial.C 2 * Polynomial.X + 1) * Polynomial.X

private theorem witnessPoly_eval (n : ℕ) : witnessPoly.eval n = (2 * n + 1) * n := by
  simp [witnessPoly]

private theorem check_correct (x : List Bool) :
    binPackingDec x ↔ ∃ w, w.length ≤ witnessPoly.eval x.length ∧ check x w := by
  cases hx : bitDecode (α := BinPackingInstance) x with
  | none => simp [binPackingDec, check, hx]
  | some i =>
    obtain ⟨as, B, k⟩ := i
    simp only [binPackingDec, check, hx, decide_eq_true_eq]
    constructor
    · intro h
      obtain ⟨ws, hk, hv, hl⟩ := Certificate.masks_bounded (as, B, k) h
      refine ⟨ws.flatMap delimit, ?_, ws, rfl, by simpa using hk, hv⟩
      have hn := decoded_fst_list_length_le hx
      rw [witnessPoly_eval]
      exact hl.trans (by dsimp; gcongr)
    · rintro ⟨w, -, ws, -, hcount, hvalid⟩
      obtain ⟨bins, hlen, hf, hc⟩ := Certificate.masks_sound B ws as hvalid
      have hk : bins.length ≤ k := by omega
      have emp (n : ℕ) : (List.replicate n ([] : List ℕ)).flatten = [] := by
        induction n with
        | zero => rfl
        | succ n ih => simp [List.replicate_succ, ih]
      refine ⟨bins ++ List.replicate (k - bins.length) [], ?_,
        by simpa [emp] using hf, ?_⟩
      · simp
        omega
      · intro b hb
        rcases List.mem_append.mp hb with hb | hb
        · exact hc b hb
        · simp [List.eq_of_mem_replicate hb]

private theorem mem_np : binPackingDec ∈ NP :=
  ⟨witnessPoly, fun p => check p.1 p.2, check_poly, check_correct⟩

end Machine

/-- **BIN PACKING is NP-complete.** The bin packing decision problem belongs to NP, and every
decision problem in NP has a polynomial-time many-one reduction to it.

Source: M. R. Garey and D. S. Johnson, *Computers and
Intractability* (1979), BIN PACKING; D. S. Johnson, "Fast algorithms for bin packing"
(1974). -/
public theorem binPacking_npComplete :
    binPackingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L binPackingDec :=
  ⟨Machine.mem_np, Hardness.npHard⟩

end MetaMathlibExt.Complexity.NPComplete.BinPacking
