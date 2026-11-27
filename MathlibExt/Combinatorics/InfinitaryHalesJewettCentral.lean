/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.InfinitaryHalesJewett
import Mathlib.Combinatorics.HalesJewett
import MathlibExt.Combinatorics.PartitionRegularUltrafilter

/-!
# Infinitary Hales–Jewett configurations in central sets

The ultrafilters all of whose members are J-sets form a nonempty two-sided ideal, so a
central set is a C-set in the same semigroup. The C-set configuration theorem then gives
the required words.

## References

* Aninda Chakraborty and Sayan Goswami, *An Analogue to the Infinitary Hales-Jewett Theorem*,
  INTEGERS 24 (2024), Article A74, Theorem 3.5 and Corollary 3.6.
* Nikolaos Karagiannis, *A combinatorial proof of an infinite version of the Hales-Jewett
  theorem*, Journal of Combinatorics 4 (2013), 273–291, Theorem 3 (the increasing-alphabet
  result that Theorem 3.5 extends to central sets).
* Aninda Chakraborty and Sayan Goswami, *Hales–Jewett type configurations in small sets*,
  European Journal of Combinatorics 104 (2022), Article 103539, Theorem 2.3 (the J-set
  configuration used by the C-set result).
* Neil Hindman and Dona Strauss, *Algebra in the Stone-Čech Compactification: Theory and
  Applications*, second edition, De Gruyter, 2012, Theorem 14.14.4, Lemma 14.14.6 and
  Corollary 14.14.10.
* John H. Johnson Jr., *A new and simpler noncommutative central sets theorem*, Topology and
  its Applications 189 (2015), 10–24, Section 2 (the J-set ideal).
* Neil Hindman and Dona Strauss, *Cartesian Products of Sets Satisfying the Central Sets
  Theorem*, Topology Proceedings 35 (2010), 203–223 (partition regularity of J-sets).
* Alfred W. Hales and Robert I. Jewett, *Regularity and Positional Games*, Transactions of the
  American Mathematical Society 106 (1963), 222–229 (Hales–Jewett theorem).
* Mauro Di Nasso and Renling Jin, *From Schur's Theorem to the Pairwise Sum Theorem*,
  INTEGERS 25 (2025), Article A105, Proposition 3.1 (ultrafilter transfer).
-/

open Filter

namespace MetaMathlibExt

attribute [local instance] Ultrafilter.semigroup

section JIdeal

variable {S : Type*} [Semigroup S]

-- The constants between variable positions can be absorbed into the adjacent coefficients.
private theorem exists_jBlocks {ι : Type*} (f : ι → ℕ → S) (s z : S) (start : ℕ)
    (w : List (Option ι)) :
    ∃ (bs : List (S × ℕ)) (b : S),
      bs.Pairwise (fun x y => x.2 < y.2) ∧ (∀ x ∈ bs, start ≤ x.2) ∧
      (none ∈ w → bs ≠ []) ∧
      ∀ i : ι, (w.zipIdx start).foldr (fun (o, t) y => (s * f (o.getD i) t) * y) z =
        bs.foldr (fun (a, t) y => (a * f i t) * y) b := by
  induction w generalizing start with
  | nil => exact ⟨[], z, by simp, by simp, by simp, fun _ => rfl⟩
  | cons o w ih =>
    obtain ⟨bs, b, hsorted, hbound, hne, heval⟩ := ih (start + 1)
    cases o with
    | none =>
      refine ⟨(s, start) :: bs, b,
        List.pairwise_cons.mpr ⟨fun x hx => hbound x hx, hsorted⟩, ?_, by simp, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with h | h
        · subst x
          exact le_rfl
        · exact Nat.le_of_succ_le (hbound x h)
      · intro i
        simp only [List.zipIdx_cons, List.foldr_cons, Option.getD_none, heval]
    | some j =>
      cases bs with
      | nil =>
        refine ⟨[], (s * f j start) * b, by simp, by simp, ?_, ?_⟩
        · simpa using hne
        · intro i
          simp only [List.zipIdx_cons, List.foldr_cons, Option.getD_some, heval, List.foldr_nil]
      | cons a as =>
        refine ⟨((s * f j start) * a.1, a.2) :: as, b, ?_, ?_, by simp, ?_⟩
        · simpa only [List.pairwise_cons] using hsorted
        · intro x hx
          rcases List.mem_cons.mp hx with h | h
          · subst x
            exact Nat.le_of_succ_le (hbound a (.head _))
          · exact Nat.le_of_succ_le (hbound x (.tail _ h))
        · intro i
          simp only [List.zipIdx_cons, List.foldr_cons, Option.getD_some]
          rw [heval]
          simp only [List.foldr_cons, mul_assoc]

private theorem jBlocks_eval (bs : List (S × ℕ)) (f : ℕ → S) (s z : S) :
    s * bs.foldr (fun (a, t) y => (a * f t) * y) z =
      bs.foldl (fun y (a, t) => y * (a * f t)) s * z := by
  induction bs generalizing s with
  | nil => rfl
  | cons a bs ih =>
    simpa only [List.foldr_cons, List.foldl_cons, mul_assoc] using ih (s * (a.1 * f a.2))

private theorem exists_mono_jPattern (s : S) {r : ℕ} (c : S → Fin r)
    (F : Finset (ℕ → S)) :
    ∃ (k : Fin r) (m : ℕ) (a : Fin (m + 2) → S) (t : Fin (m + 1) → ℕ),
      StrictMono t ∧ ∀ f ∈ F,
        c ((List.ofFn fun j : Fin m => a j.succ.castSucc * f (t j.succ)).foldl (· * ·)
          (a 0 * f (t 0)) * a (Fin.last (m + 1))) = k := by
  classical
  obtain ⟨ι, _, hHJ⟩ := Combinatorics.Line.exists_mono_in_high_dimension F (Fin r)
  let e := Fintype.equivFin ι
  let col (v : ι → F) := c ((List.ofFn fun j => v (e.symm j)).zipIdx.foldr
    (fun (g, t) y => (s * (g : ℕ → S) t) * y) s)
  obtain ⟨l, k, hk⟩ := hHJ col
  let w := List.ofFn fun j => l.idxFun (e.symm j)
  obtain ⟨j, hj⟩ := l.proper
  have hw : none ∈ w := List.mem_ofFn.mpr ⟨e j, by simpa using hj⟩
  obtain ⟨bs, b, hsorted, _, hne, heval⟩ := exists_jBlocks Subtype.val s s 0 w
  obtain ⟨a, as, rfl⟩ := List.exists_cons_of_ne_nil (hne hw)
  let B (i : Fin (as.length + 1)) := (a :: as).get i
  let t (i : Fin (as.length + 1)) := (B i).2
  let coeff (i : Fin (as.length + 2)) : S := Fin.lastCases b (fun i => (B i).1) i
  refine ⟨k, as.length, coeff, t, ?_, ?_⟩
  · exact fun i j hij => List.pairwise_iff_get.mp hsorted _ _ hij
  · intro f hf
    let g : F := ⟨f, hf⟩
    have hcol : col (l g) = k := hk g
    have hzip : (w.zipIdx 0).map (Prod.map (fun o => o.getD g) id) =
        (List.ofFn fun j => l g (e.symm j)).zipIdx 0 := by
      rw [List.map_zipIdx, List.map_ofFn]
      rfl
    have hcolor : col (l g) = c ((a :: as).foldr (fun (u, i) y => (u * f i) * y) b) := by
      unfold col
      rw [← hzip, List.foldr_map]
      exact congrArg c (heval g)
    have hrest : List.ofFn (fun j : Fin as.length => coeff j.succ.castSucc * f (t j.succ)) =
        as.map (fun (u, i) => u * f i) := by
      simp only [coeff, Fin.lastCases_castSucc, t, B]
      change List.ofFn ((fun (u, i) => u * f i) ∘ as.get) = _
      rw [← List.map_ofFn, List.ofFn_get]
    have hfold := jBlocks_eval as f (a.1 * f a.2) b
    rw [← List.foldl_map] at hfold
    have hzero : coeff 0 = a.1 := by
      change coeff ((0 : Fin (as.length + 1)).castSucc) = a.1
      simp only [coeff, Fin.lastCases_castSucc, B, List.get_cons_zero]
    rw [hrest, hzero]
    simp only [coeff, Fin.lastCases_last, t, B, List.get_cons_zero]
    rw [← hfold]
    exact hcolor.symm.trans hcol

private theorem exists_jSet_ultrafilter (s : S) :
    ∃ p : Ultrafilter S, ∀ D ∈ p, IsMulJSet D := by
  classical
  obtain ⟨p, hp⟩ := (weaklyPartitionRegular_iff_exists_ultrafilter {D : Set S | IsMulJSet D}).mp
    (by
      intro r c
      suffices ∃ k : Fin r, IsMulJSet {x | c x = k} by
        obtain ⟨k, hk⟩ := this
        exact ⟨_, hk, k, fun _ hx => hx⟩
      by_contra! h
      have hbad (k : Fin r) : ∃ F : Finset (ℕ → S), F.Nonempty ∧
          ¬ ∃ (m : ℕ) (a : Fin (m + 2) → S) (t : Fin (m + 1) → ℕ),
            StrictMono t ∧ ∀ f ∈ F,
              c ((List.ofFn fun j : Fin m => a j.succ.castSucc * f (t j.succ)).foldl (· * ·)
                (a 0 * f (t 0)) * a (Fin.last (m + 1))) = k := by
        have hn := h k
        rw [IsMulJSet, not_forall] at hn
        exact hn.imp fun F hF => not_imp.mp hF
      choose F _ hF using hbad
      let G := Finset.univ.biUnion F
      obtain ⟨k, m, a, t, ht, hmono⟩ := exists_mono_jPattern s c G
      exact hF k ⟨m, a, t, ht, fun f hf =>
        hmono f (Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ k, hf⟩)⟩)
  refine ⟨p, fun D hD => ?_⟩
  obtain ⟨E, hE, hsub⟩ := hp D hD
  intro F hF
  obtain ⟨m, a, t, ht, ha⟩ := hE F hF
  exact ⟨m, a, t, ht, fun f hf => hsub (ha f hf)⟩

private theorem isCSet_of_central {D : Set S} (hD : IsCentralSet D) : IsCSet D := by
  classical
  obtain ⟨p, hp, hmin, hD⟩ := hD
  let I : Set (Ultrafilter S) := {q | ∀ E ∈ q, IsMulJSet E}
  have hI : I.Nonempty := exists_jSet_ultrafilter (Ultrafilter.nonempty_of_mem hD).some
  refine ⟨p, hp, hmin I hI (fun q hq r => ⟨?_, ?_⟩), hD⟩
  · intro E hE F hF
    change {x | {y | x * y ∈ E} ∈ q} ∈ r at hE
    obtain ⟨x, hx⟩ := Ultrafilter.nonempty_of_mem hE
    obtain ⟨m, a, t, ht, ha⟩ := hq _ hx F hF
    let coeff : Fin (m + 2) → S := Fin.cases (x * a 0) (a ∘ Fin.succ)
    refine ⟨m, coeff, t, ht, fun f hf => ?_⟩
    have hsucc (j : Fin (m + 1)) : coeff j.succ = a j.succ := Fin.cases_succ j
    have hfirst (j : Fin m) : coeff j.succ.castSucc = a j.succ.castSucc := hsucc j.castSucc
    have hzero : coeff 0 = x * a 0 := Fin.cases_zero
    have hlast : coeff (Fin.last (m + 1)) = a (Fin.last (m + 1)) := hsucc (Fin.last m)
    simpa only [Set.mem_ofPred_eq, hfirst, hzero, hlast, mul_assoc, List.foldl_assoc] using ha f hf
  · intro E hE F hF
    change {x | {y | x * y ∈ E} ∈ r} ∈ q at hE
    obtain ⟨m, a, t, ht, ha⟩ := hq _ hE F hF
    let P (f : ℕ → S) := (List.ofFn fun j : Fin m => a j.succ.castSucc * f (t j.succ)).foldl
      (· * ·) (a 0 * f (t 0))
    have htail : ∀ᶠ y in r, ∀ f ∈ F, (P f * a (Fin.last (m + 1))) * y ∈ E :=
      (Filter.eventually_all_finset F).mpr ha
    obtain ⟨y, hy⟩ := Ultrafilter.nonempty_of_mem htail
    let coeff : Fin (m + 2) → S := Fin.lastCases (a (Fin.last (m + 1)) * y) (a ∘ Fin.castSucc)
    refine ⟨m, coeff, t, ht, fun f hf => ?_⟩
    have hcast (j : Fin (m + 1)) : coeff j.castSucc = a j.castSucc := Fin.lastCases_castSucc j
    have hzero : coeff 0 = a 0 := hcast 0
    have hlast : coeff (Fin.last (m + 1)) = a (Fin.last (m + 1)) * y := Fin.lastCases_last
    simpa only [hcast, hzero, hlast, P, ← mul_assoc] using hy f hf

end JIdeal

/-- **Infinitary Hales–Jewett configurations in central sets.** Let
$A_0 \subseteq A_1 \subseteq \cdots$ be finite sets with union $A$, and let $S_0$ be the semigroup
of nonempty finite words over $A$ under concatenation. For $n \in \mathbb{N}$, an $n$-variable
word over $A$ is a nonempty finite word over $A \cup \{v_0, \dots, v_{n-1}\}$, for distinct
variables $v_i \notin A$, in which every $v_i$ occurs; for $\vec a = (a_0, \dots, a_{n-1})$ in
$A^n$, the word $w(\vec a) \in S_0$ is obtained from $w$ by replacing each $v_i$ by $a_i$. If
$D \subseteq S_0$ is central, then for every $n \in \mathbb{N}$ there is a sequence
$w_0, w_1, \dots$ of $n$-variable words over $A$ such that
$w_{m_0}(\vec a_0) w_{m_1}(\vec a_1) \cdots w_{m_l}(\vec a_l) \in D$ for all $l \in \mathbb{N}$,
all $m_0 < m_1 < \cdots < m_l$ in $\mathbb{N}$ and all $\vec a_j \in A_{m_j}^n$,
$j = 0, \dots, l$.

Source: Aninda Chakraborty and Sayan Goswami, *An Analogue to the Infinitary Hales–Jewett
Theorem*, INTEGERS 24 (2024), Article A74, Theorem 3.5. -/
public theorem exists_variableWords_prod_mem_of_isCentralSet {α : Type*}
    (A : ℕ → Finset α) (hA : Monotone A) (hcover : ∀ x, ∃ i, x ∈ A i) (n : ℕ)
    {D : Set (FreeSemigroup α)} (hD : IsCentralSet D) :
    ∃ w : ℕ → FreeSemigroup (α ⊕ Fin n), (∀ k i, Sum.inr i ∈ (w k).head :: (w k).tail) ∧
      ∀ (l : ℕ) (m : Fin (l + 1) → ℕ) (a : Fin (l + 1) → Fin n → α), StrictMono m →
        (∀ j i, a j i ∈ A (m j)) →
        (List.ofFn fun j : Fin l => FreeSemigroup.map (Sum.elim id (a j.succ)) (w (m j.succ))).foldl
          (· * ·) (FreeSemigroup.map (Sum.elim id (a 0)) (w (m 0))) ∈ D :=
  exists_variableWords_prod_mem_of_isCSet A hA hcover n (isCSet_of_central hD)

end MetaMathlibExt
