/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Composition
public import MathlibExt.Combinatorics.Enumerative.SchreierSparseCount
import Mathlib.Data.List.Pairwise

/-!
# Counting strong Schreier sets by compositions

`strongSchreierCount_eq` counts the `ℓ`-strong Schreier sets with maximum `n` by the
compositions of `n + ℓ` with parts greater than `ℓ`. For a composition with `k` parts,
start at `ℓ * (k - 1)` and take successive steps of size `part - ℓ`. The endpoints form the set.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.Combinatorics.Enumerative.SchreierTypeSetsWanted

/-- **Number of strong Schreier sets with a given maximum.** For natural numbers $n$ and $\ell$,
$|B_{n,\ell}|$ is the number of sets $B \subseteq \{1, \dots, n\}$ with $n \in B$ that are
$\ell$-strong Schreier, that is, every element of $B$ is at least $\ell|B| - \ell + 1$. -/
def strongSchreierCount (n l : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.filter (fun B => n ∈ B ∧
    IsStrongSchreier l B)).card

/-- **Compositions with parts at least $v$.** For natural numbers $u$ and $v$, $c(u, v)$ is the
number of compositions of $u$ (ordered sequences of positive integers summing to $u$) all of
whose parts are at least $v$. -/
def compositionMinPartCount (u v : ℕ) : ℕ :=
  Fintype.card {c : Composition u // ∀ x ∈ c.blocks, v ≤ x}

namespace strongSchreierCount_eq

private def endpoints (l a : ℕ) : List ℕ → List ℕ
  | [] => []
  | b :: bs =>
    let x := a + (b - l)
    x :: endpoints l x bs

private theorem length_endpoints (l a : ℕ) (bs : List ℕ) :
    (endpoints l a bs).length = bs.length := by
  induction bs generalizing a with
  | nil => rfl
  | cons b bs ih => simp [endpoints, ih]

-- The endpoints increase strictly. The last one recovers the sum after restoring
-- the amount subtracted from each part.
private theorem endpoints_spec {l : ℕ} (a : ℕ) {bs : List ℕ}
    (hb : ∀ b ∈ bs, l + 1 ≤ b) :
    (a :: endpoints l a bs).Pairwise (· < ·) ∧
      (a :: endpoints l a bs).getLast (by simp) + l * bs.length = a + bs.sum := by
  induction bs generalizing a with
  | nil => simp [endpoints]
  | cons b bs ih =>
    have h := hb b (.head _)
    obtain ⟨hs, he⟩ := ih (a + (b - l)) (fun x hx => hb x (.tail _ hx))
    simp only [endpoints, List.pairwise_cons_cons_iff_of_trans, List.getLast_cons_cons,
      List.length_cons, Nat.mul_succ, List.sum_cons]
    exact ⟨⟨by omega, hs⟩, by omega⟩

private theorem endpoints_inj {l a : ℕ} {bs cs : List ℕ}
    (hb : ∀ b ∈ bs, l + 1 ≤ b) (hc : ∀ c ∈ cs, l + 1 ≤ c)
    (he : endpoints l a bs = endpoints l a cs) : bs = cs := by
  induction bs generalizing a cs with
  | nil => cases cs <;> simp_all [endpoints]
  | cons b bs ih =>
    cases cs with
    | nil => simp [endpoints] at he
    | cons c cs =>
      obtain ⟨hx, ht⟩ := List.cons.inj he
      have hbc : b = c := by
        have := hb b (.head _)
        have := hc c (.head _)
        change a + (b - l) = a + (c - l) at hx
        omega
      subst c
      exact congrArg (b :: ·) (ih (fun x hx => hb x (.tail _ hx))
        (fun x hx => hc x (.tail _ hx)) ht)

private theorem exists_endpoints {l a : ℕ} {xs : List ℕ}
    (hs : (a :: xs).Pairwise (· < ·)) :
    ∃ bs, (∀ b ∈ bs, l + 1 ≤ b) ∧ endpoints l a bs = xs := by
  induction xs generalizing a with
  | nil => exact ⟨[], by simp, rfl⟩
  | cons x xs ih =>
    obtain ⟨hax, ht⟩ := List.pairwise_cons_cons_iff_of_trans.mp hs
    obtain ⟨bs, hb, he⟩ := ih ht
    refine ⟨(x - a + l) :: bs, ?_, ?_⟩
    · exact List.forall_mem_cons.mpr ⟨by omega, hb⟩
    · simpa [endpoints, Nat.add_sub_of_le hax.le] using congrArg (x :: ·) he

private abbrev family (n l : ℕ) :=
  (Finset.Icc 1 n).powerset.filter (fun B => n ∈ B ∧ IsStrongSchreier l B)

private abbrev parts (n l : ℕ) := {c : Composition (n + l) // ∀ b ∈ c.blocks, l + 1 ≤ b}

private theorem offset_add (l : ℕ) {k : ℕ} (hk : 0 < k) : l * (k - 1) + l = l * k := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  simp [Nat.mul_succ]

private def toSet {n l : ℕ} (hn : 1 ≤ n) (c : parts n l) : family n l := by
  let a := l * (c.val.length - 1)
  let xs := endpoints l a c.val.blocks
  have hk := c.val.length_pos_iff.mpr (show 0 < n + l by omega)
  have ha : a + l = l * c.val.length := offset_add l hk
  obtain ⟨hs, he⟩ := endpoints_spec a c.property
  have hlen : xs.length = c.val.length := length_endpoints _ _ _
  have hxs : xs ≠ [] := List.ne_nil_of_length_pos (hlen.trans_gt hk)
  have hlast : xs.getLast hxs = n := by
    rw [List.getLast_cons hxs, c.val.blocks_sum] at he
    change xs.getLast hxs + l * c.val.length = a + (n + l) at he
    omega
  obtain ⟨hlo, hsort⟩ := List.pairwise_cons.mp hs
  have hcard : xs.toFinset.card = c.val.length :=
    (List.toFinset_card_of_nodup hsort.sortedLT.nodup).trans hlen
  refine ⟨xs.toFinset, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, ?_, ?_⟩⟩
  · intro x hx
    have hx' := List.mem_toFinset.mp hx
    have hax := hlo x hx'
    exact Finset.mem_Icc.mpr ⟨by omega, (hsort.sortedLT.sortedLE.pairwise.rel_getLast hx').trans_eq
      hlast⟩
  · exact List.mem_toFinset.mpr (hlast ▸ List.getLast_mem hxs)
  · intro x hx
    have := hlo x (List.mem_toFinset.mp hx)
    rw [hcard]
    omega

private theorem toSet_bijective {n l : ℕ} (hn : 1 ≤ n) :
    Function.Bijective (toSet (l := l) hn) := by
  constructor
  · intro c d h
    have sorted (v : parts n l) : (toSet hn v).val.sort =
        endpoints l (l * (v.val.length - 1)) v.val.blocks := by
      have hs := (endpoints_spec (l * (v.val.length - 1)) v.property).1.tail.sortedLT
      exact (List.toFinset_sort _ hs.nodup).mpr hs.sortedLE.pairwise
    have he := congrArg (fun B : family n l => B.val.sort) h
    rw [sorted, sorted] at he
    have hlen : c.val.length = d.val.length := by
      simpa only [length_endpoints] using congrArg List.length he
    rw [hlen] at he
    exact Subtype.ext (Composition.ext (endpoints_inj c.property d.property he))
  · rintro ⟨B, hB⟩
    obtain ⟨hsub, hnB, hstrong⟩ := Finset.mem_filter.mp hB
    replace hsub := Finset.mem_powerset.mp hsub
    let a := l * (B.card - 1)
    have ha : a + l = l * B.card := offset_add l (Finset.card_pos.mpr ⟨n, hnB⟩)
    have hs : (a :: B.sort).Pairwise (· < ·) := by
      refine List.pairwise_cons.mpr ⟨?_, B.sortedLT_sort.pairwise⟩
      intro x hx
      have := hstrong x ((Finset.mem_sort _).mp hx)
      omega
    obtain ⟨bs, hb, he⟩ := exists_endpoints (l := l) hs
    have hlen : bs.length = B.card := by simpa [length_endpoints] using congrArg List.length he
    have hnSort : n ∈ B.sort := (Finset.mem_sort _).mpr hnB
    have hne := List.ne_nil_of_mem hnSort
    have hlast : B.sort.getLast hne = n :=
      le_antisymm (Finset.mem_Icc.mp (hsub ((Finset.mem_sort _).mp (List.getLast_mem hne)))).2
        ((B.pairwise_sort (· ≤ ·)).rel_getLast hnSort)
    have htotal := (endpoints_spec a hb).2
    rw [he, List.getLast_cons hne, hlast, hlen] at htotal
    let c : Composition (n + l) :=
      ⟨bs, fun hx => (Nat.zero_lt_succ l).trans_le (hb _ hx), by omega⟩
    refine ⟨⟨c, hb⟩, Subtype.ext ?_⟩
    change (endpoints l (l * (bs.length - 1)) bs).toFinset = B
    simpa [hlen, a] using congrArg List.toFinset he

end strongSchreierCount_eq

/-- **Strong Schreier sets with a given maximum are counted by compositions.** For all natural
numbers $n \ge 1$ and $\ell \ge 0$, the number $|B_{n,\ell}|$ of $\ell$-strong Schreier sets
$B \subseteq \{1, \dots, n\}$ with $n \in B$ equals $c(n + \ell, \ell + 1)$, the number of
compositions of $n + \ell$ into parts that are all at least $\ell + 1$. Here a set $B$ is
$\ell$-strong Schreier when every element of $B$ is at least $\ell|B| - \ell + 1$.

Source: Kevin Beanland and Hùng Việt Chu, "On Schreier-Type
Sets, Partitions, and Compositions", Theorem 9. -/
theorem strongSchreierCount_eq (n l : ℕ) (hn : 1 ≤ n) :
    strongSchreierCount n l = compositionMinPartCount (n + l) (l + 1) := by
  unfold strongSchreierCount compositionMinPartCount
  rw [← Fintype.card_coe]
  exact Fintype.card_congr (Equiv.ofBijective _ (strongSchreierCount_eq.toSet_bijective hn)).symm

end MathlibExt.Combinatorics.Enumerative.SchreierTypeSetsWanted
