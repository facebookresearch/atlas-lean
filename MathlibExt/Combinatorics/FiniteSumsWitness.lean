/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Hindman
public import Mathlib.Data.PNat.Basic
import Mathlib.Data.Nat.Log

/-!
# Ultrafilter witnesses of the finite sums family

An ultrafilter on the positive integers lies in the closure of the additive idempotents exactly
when each of its members contains all nonempty finite sums of some infinite set.
-/

open Filter Hindman

namespace MetaMathlibExt

namespace finiteSums_witness_iff_mem_closure_idempotents

attribute [local instance] Ultrafilter.add

/-- An injective stream uses distinct values in every finite sum. -/
private theorem finset_of_FS {a : Stream' ℕ+} {y : ℕ+} (hy : FS a y)
    (ha : Function.Injective a.get) :
    ∃ F : Finset ℕ+, F.Nonempty ∧ (F : Set ℕ+) ⊆ Set.range a.get ∧
      (y : ℕ) = ∑ x ∈ F, (x : ℕ) := by
  induction hy with
  | head a => exact ⟨{a.head}, by simp, by simp, by simp⟩
  | of_tail a y _ ih =>
    obtain ⟨F, hF, hsub, hsum⟩ := ih (ha.comp Nat.succ_injective)
    exact ⟨F, hF, hsub.trans (Set.range_comp_subset_range Nat.succ a.get), hsum⟩
  | cons a y _ ih =>
    obtain ⟨F, hF, hsub, hsum⟩ := ih (ha.comp Nat.succ_injective)
    have hfresh : a.head ∉ F := by
      intro h
      obtain ⟨i, hi⟩ := hsub h
      exact Nat.succ_ne_zero i (ha hi)
    refine ⟨insert a.head F, Finset.insert_nonempty .., ?_, ?_⟩
    · rw [Finset.coe_insert, Set.insert_subset_iff]
      exact ⟨⟨0, rfl⟩, hsub.trans (Set.range_comp_subset_range Nat.succ a.get)⟩
    · rw [Finset.sum_insert hfresh, PNat.add_coe, hsum]

/-- Lift a finite sum of the underlying naturals back to the positive integers. -/
private theorem lift_FS {b : Stream' ℕ} {n : ℕ} (hn : FS b n) :
    ∀ a : Stream' ℕ+, b = a.map (↑) → ∃ y : ℕ+, FS a y ∧ (y : ℕ) = n := by
  induction hn with
  | head b => rintro a rfl; exact ⟨a.head, FS.head a, rfl⟩
  | of_tail b m _ ih =>
    rintro a rfl
    obtain ⟨y, hy, rfl⟩ := ih a.tail rfl
    exact ⟨y, FS.of_tail a y hy, rfl⟩
  | cons b m _ ih =>
    rintro a rfl
    obtain ⟨y, hy, rfl⟩ := ih a.tail rfl
    exact ⟨a.head + y, FS.cons a y hy, rfl⟩

/-- Restrict to a colour class that separates each number from its double. Any stream whose
finite sums lie in this class is injective. -/
private theorem exists_injective_FS (V : Ultrafilter ℕ+)
    (hid : V + V = V) {A : Set ℕ+} (hA : A ∈ V) :
    ∃ a : Stream' ℕ+, Function.Injective a.get ∧ ∀ y, FS a y → y ∈ A := by
  let c (x : ℕ+) : Fin 2 := ⟨Nat.log 2 x % 2, Nat.mod_lt _ (by decide)⟩
  have hdouble (x : ℕ+) : c (x + x) ≠ c x := by
    intro h
    have heq := congrArg Fin.val h
    change Nat.log 2 ((x : ℕ) + x) % 2 = Nat.log 2 x % 2 at heq
    rw [← Nat.mul_two, Nat.log_mul_base Nat.one_lt_two (n := (x : ℕ)) x.2.ne'] at heq
    omega
  obtain ⟨k, hk⟩ : ∃ k, ∀ᶠ x in V, c x = k :=
    Ultrafilter.eventually_exists_iff.mp (Eventually.of_forall fun x => ⟨c x, rfl⟩)
  obtain ⟨a, ha⟩ := exists_FS_of_large V hid (A ∩ {x | c x = k}) (inter_mem hA hk)
  have hne (i j : ℕ) (hij : i < j) : a.get i ≠ a.get j := by
    intro heq
    have hpair := (ha _ (FS.add_two a i j hij)).2
    rw [heq] at hpair
    exact hdouble _ (hpair.trans (ha _ (FS.singleton a j)).2.symm)
  refine ⟨a, ?_, fun y hy => (ha y hy).1⟩
  intro i j h
  rcases lt_trichotomy i j with hij | hij | hji
  · exact (hne i j hij h).elim
  · exact hij
  · exact (hne j i hji h.symm).elim

end finiteSums_witness_iff_mem_closure_idempotents

open finiteSums_witness_iff_mem_closure_idempotents in
/-- **PR-witnesses of the finite sums family.** Let $\beta\mathbb{N}^+$ be the space of
ultrafilters on the positive integers $\mathbb{N}^+$, with the Stone–Čech topology and the sum
for which $A \in U + V$ if and only if $\{n : \{m : n + m \in A\} \in V\} \in U$. For
$X \subseteq \mathbb{N}^+$ let $\mathrm{FS}(X)$ be the set of sums of nonempty finite subsets of
$X$. An ultrafilter $U \in \beta\mathbb{N}^+$ is a PR-witness of the Hindman family, that is,
every $A \in U$ contains $\mathrm{FS}(X)$ for some infinite $X \subseteq \mathbb{N}^+$, if and
only if $U$ lies in the closure of the set of idempotents $\{V \in \beta\mathbb{N}^+ : V + V = V\}$.

Source: Mauro Di Nasso and Renling Jin, *From Schur's Theorem to the Pairwise Sum Theorem*,
INTEGERS 25 (2025), Article A105, Proposition 3.3 (`integers-2025-A105-prop-3-3`), quoting
Hindman and Strauss, Lemma 5.19. -/
public theorem finiteSums_witness_iff_mem_closure_idempotents (U : Ultrafilter ℕ+) :
    letI : Add (Ultrafilter ℕ+) := Ultrafilter.add
    (∀ A ∈ U, ∃ X : Set ℕ+, X.Infinite ∧
        ∀ F : Finset ℕ+, F.Nonempty → (F : Set ℕ+) ⊆ X →
          ∃ y ∈ A, (y : ℕ) = ∑ x ∈ F, (x : ℕ)) ↔
      U ∈ closure {V : Ultrafilter ℕ+ | V + V = V} := by
  classical
  rw [ultrafilterBasis_is_basis.mem_closure_iff]
  constructor
  · rintro hU _ ⟨A, rfl⟩ hA
    obtain ⟨X, hX, hsums⟩ := hU A hA
    let e := hX.natEmbedding X
    let a : Stream' ℕ+ := fun i => e i
    have hinj : Function.Injective a.get := Subtype.val_injective.comp e.injective
    obtain ⟨V, hid, hV⟩ := exists_idempotent_ultrafilter_le_FS a
    refine ⟨V, mem_of_superset hV ?_, hid⟩
    intro y hy
    obtain ⟨F, hF, hsub, hsum⟩ := finset_of_FS hy hinj
    obtain ⟨z, hz, hzeq⟩ := hsums F hF (hsub.trans (Set.range_subset_iff.mpr fun i => (e i).2))
    exact Subtype.ext (hzeq.trans hsum.symm) ▸ hz
  · intro hU A hA
    obtain ⟨V, hAV, hid⟩ := hU _ ⟨A, rfl⟩ hA
    obtain ⟨a, hinj, ha⟩ := exists_injective_FS V hid hAV
    refine ⟨Set.range a.get, Set.infinite_range_of_injective hinj, ?_⟩
    intro F hF hsub
    rw [← Set.image_univ] at hsub
    obtain ⟨I, _, rfl⟩ := Finset.subset_set_image_iff.mp hsub
    rw [Finset.sum_image hinj.injOn]
    have hI := Finset.image_nonempty.mp hF
    obtain ⟨y, hy, hsum⟩ := lift_FS (FS.finsetSum (a.map (↑) : Stream' ℕ) I hI) a rfl
    exact ⟨y, ha y hy, hsum⟩

end MetaMathlibExt
