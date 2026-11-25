/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Bioinformatics.Phylogenetics.QuartetSupport
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Tests for quartet support: a strict-plurality frequency vector with plurality value
`2/5 < 1/2` whose unique support maximizer is the species tree; on five taxa there are 15
trees, distinguished by their quartets; and a tie example showing strict plurality cannot
be dropped. -/

open MathlibExt.Biology.Phylogenetics.UnrootedTreeCount

namespace CSLibExtTest.Bioinformatics.Phylogenetics.QuartetSupport

open Cslib.Bioinformatics.Phylogenetics.Splits

section QuartetSupport

variable {X : Type} [Fintype X] [DecidableEq X]

open Classical in
/-- Frequencies `2/5` on the species resolution and `3/10` on each other resolution. -/
noncomputable def pluralityFreq (S : UnrootedBinaryTree X) (q : Finset X)
    (ρ : Finset (Finset X)) : ℝ :=
  if Induces S q ρ then 2 / 5 else 3 / 10


example [Nonempty X] (S : UnrootedBinaryTree X) :
    (2 / 5 : ℝ) < 1 / 2 ∧
      (∀ q ∈ quartets, ∑ ρ ∈ resolutions q, pluralityFreq S q ρ = 1) ∧
      IsStrictPlurality (pluralityFreq S) S ∧
      ∀ T : UnrootedBinaryTree X, ¬ T.Iso S →
        quartetScore (pluralityFreq S) T < quartetScore (pluralityFreq S) S := by
  classical
  have hplur : IsStrictPlurality (pluralityFreq S) S := by
    intro q _ ρ _ σ _ hρ hσ
    simp only [pluralityFreq, hρ, hσ, ite_true, ite_false]
    norm_num
  refine ⟨by norm_num, fun q hq => ?_, hplur, fun T hT => quartetScore_lt_of_not_iso hplur hT⟩
  have h1 := card_filter_induces S hq
  have h3 := card_resolutions hq
  have hsplit := Finset.card_filter_add_card_filter_not (s := resolutions q) (Induces S q)
  simp only [pluralityFreq]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, h1]
  have h2 : ((resolutions q).filter fun ρ => ¬ Induces S q ρ).card = 2 := by omega
  rw [h2]
  norm_num

/-- Acceptance 1 (five taxa): there are `15` unrooted binary trees on five labeled taxa up to
isomorphism (Atlas `nat_card_unrootedBinaryTree`), and trees inducing the same quartet trees are
isomorphic, so the `15` trees are distinguished by their quartets. -/
example : Nat.card (Quot (UnrootedBinaryTree.Iso (X := Fin 5))) = 15 ∧
    ∀ S T : UnrootedBinaryTree (Fin 5),
      (∀ q ∈ quartets, ∀ ρ ∈ resolutions q, (Induces T q ρ ↔ Induces S q ρ)) → T.Iso S :=
  ⟨by rw [nat_card_unrootedBinaryTree 5 (by norm_num)]; decide, fun _ _ h => iso_of_induces_iff h⟩

/-- Non-vacuity: on five taxa there are two non-isomorphic unrooted binary trees. -/
theorem exists_not_iso_fin_five : ∃ S T : UnrootedBinaryTree (Fin 5), ¬ T.Iso S := by
  have hcard : 1 < Nat.card (Quot (UnrootedBinaryTree.Iso (X := Fin 5))) := by
    rw [nat_card_unrootedBinaryTree 5 (by norm_num)]; decide
  have hfin : Finite (Quot (UnrootedBinaryTree.Iso (X := Fin 5))) :=
    Nat.finite_of_card_ne_zero (by omega)
  have hnt := Finite.one_lt_card_iff_nontrivial.1 hcard
  obtain ⟨c₁, c₂, hne⟩ := exists_pair_ne (Quot (UnrootedBinaryTree.Iso (X := Fin 5)))
  obtain ⟨S, rfl⟩ := Quot.exists_rep c₁
  obtain ⟨T, rfl⟩ := Quot.exists_rep c₂
  exact ⟨S, T, fun h => hne (Quot.sound h).symm⟩

/-- Boundary: without strict plurality uniqueness fails. With all three resolutions equally
frequent (`1/3`, the zero-internal-length case of the multispecies coalescent), every tree has
the same total support, and two non-isomorphic trees on five taxa tie. -/
example : ∃ S T : UnrootedBinaryTree (Fin 5), ¬ T.Iso S ∧
    quartetScore (fun _ _ => (1 / 3 : ℝ)) T = quartetScore (fun _ _ => (1 / 3 : ℝ)) S := by
  classical
  obtain ⟨S, T, hne⟩ := exists_not_iso_fin_five
  refine ⟨S, T, hne, ?_⟩
  unfold quartetScore
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [Finset.sum_const, Finset.sum_const, card_filter_induces T hq, card_filter_induces S hq]



open Cslib.Bioinformatics.Phylogenetics.Splits

end QuartetSupport

end CSLibExtTest.Bioinformatics.Phylogenetics.QuartetSupport
