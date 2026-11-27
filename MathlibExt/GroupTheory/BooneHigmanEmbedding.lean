/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/GroupTheory/BooneHigmanEmbedding.lean` (leanprover/lean-eval, commit
38361be884302c7edce1908c4aef8296eb2cb27e), for the embedding criterion for a solvable word problem.
Copyright 2026 Lean FRO, LLC.
Author (benchmark submitter): Kim Morrison.
The source manifest is `manifests/problems/boone_higman_embedding.toml`, rev 1 (archived).
lean-eval ships no `NOTICE` file. ATLAS proves the adapted statement in its existing namespace.
Mathematical statements are unchanged except that the source's extra finite-normal-generation
hypothesis on `ker φ` is dropped, matching the cited Boone–Higman theorem.
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import MathlibExt.GroupTheory.WordProblemSolvableShared
public import Mathlib.GroupTheory.FinitelyPresentedGroup
public import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Computability.Primrec.List
import Mathlib.GroupTheory.FreeGroup.Reduce
import MathlibExt.Computability.RE

/-!
# Boone–Higman theorem (easy direction)

`boone_higman_embedding`: if a finitely generated group `G` embeds in a simple
group `H` that embeds in a finitely presented group `K`, then `G` has a solvable
word problem — the "if" half of the Boone–Higman characterisation. The trusted
helper `WordProblemSolvable` (a non-hole) expresses decidability of "a word
represents the identity" via `ComputablePred`. Mathlib has finitely-presented
groups, free groups, simple groups, and computability, but no notion of the word
problem or the Boone–Higman theorem. (The main Kuznetsov/Boone–Higman, Novikov,
and Higman-infinite-simple statements of §122 are already in lean-eval.)

Category-(b) candidate from §122 of the Knill survey (additional statement 1).
-/

public section

open MathlibExt.GroupTheory.WordProblemSolvableShared

namespace MathlibExt.GroupTheory.BooneHigmanEmbeddingWanted.GroupTheory.BooneHigmanEmbedding

open FreeGroup

private abbrev Word (n : ℕ) := List (Fin n × Bool)

-- A factor specifies a conjugator, a relator, and whether to use the relator or its inverse.
private abbrev Factor (n : ℕ) := Word n × Word n × Bool

private def conjugateWord {n : ℕ} (c : Factor n) : Word n :=
  c.1 ++ ((cond c.2.2 c.2.1 (invRev c.2.1)) ++ invRev c.1)

private theorem primrec_reduce {n : ℕ} : Primrec (reduce : Word n → Word n) := by
  open Primrec in
  have step : Primrec (fun p : (Fin n × Bool) × Word n =>
      List.casesOn (motive := fun _ => Word n) p.2 [p.1] fun hd tl =>
        if p.1.1 = hd.1 ∧ p.1.2 = !hd.2 then tl else p.1 :: hd :: tl) := by
    refine list_casesOn (α := (Fin n × Bool) × Word n) (β := Fin n × Bool) (σ := Word n)
      (h := fun p q => if p.1.1 = q.1.1 ∧ p.1.2 = !q.1.2 then q.2 else p.1 :: q.1 :: q.2)
      snd (list_cons.comp fst (const ([] : Word n))) ?_
    have hfirst : Primrec (fun p : ((Fin n × Bool) × Word n) × ((Fin n × Bool) × Word n) =>
        p.1.1) := fst.comp fst
    have hnext : Primrec (fun p : ((Fin n × Bool) × Word n) × ((Fin n × Bool) × Word n) =>
        p.2.1) := fst.comp snd
    have hgen := Primrec.eq.comp (fst.comp hfirst) (fst.comp hnext)
    have hsign := Primrec.eq.comp (snd.comp hfirst) (Primrec.not.comp (snd.comp hnext))
    exact (Primrec.ite (hgen.and hsign) (snd.comp snd)
      (list_cons.comp (fst.comp fst) (list_cons.comp (fst.comp snd) (snd.comp snd)))).to₂
  refine (Primrec.list_foldr Primrec.id (Primrec.const []) (step.comp₂ Primrec₂.right)).of_eq ?_
  intro w
  simp only [id_eq]
  induction w with
  | nil => rfl
  | cons a w ih => rw [List.foldr_cons, ih, reduce.cons]

private theorem primrec_invRev {n : ℕ} : Primrec (invRev : Word n → Word n) :=
  Primrec.list_reverse.comp
    (Primrec.list_map Primrec.id
      ((Primrec.fst.pair (Primrec.not.comp Primrec.snd)).comp₂ Primrec₂.right))

private theorem primrec_conjugateWord {n : ℕ} : Primrec (conjugateWord : Factor n → Word n) := by
  unfold conjugateWord
  open Primrec in
  exact list_append.comp fst (list_append.comp
    (Primrec.cond (snd.comp snd) (fst.comp snd) (primrec_invRev.comp (fst.comp snd)))
    (primrec_invRev.comp fst))

private def relatorSet {n : ℕ} (rs : List (Word n)) : Set (FreeGroup (Fin n)) :=
  mk '' {r | r ∈ rs}

private theorem mk_conjugateWord {n : ℕ} (c r : Word n) (b : Bool) :
    mk (conjugateWord (c, r, b)) = mk c * (cond b (mk r) (mk r)⁻¹) * (mk c)⁻¹ := by
  cases b <;> simp [conjugateWord, FreeGroup.inv_mk]

private theorem mem_normalClosure_iff {n : ℕ} (rs : List (Word n)) (x : FreeGroup (Fin n)) :
    x ∈ Subgroup.normalClosure (relatorSet rs) ↔
      ∃ cs : List (Factor n), (∀ c ∈ cs, c.2.1 ∈ rs) ∧ mk (cs.flatMap conjugateWord) = x := by
  constructor
  · intro hx
    let s := Group.conjugatesOfSet (relatorSet rs)
    let P (y : FreeGroup (Fin n)) : Prop :=
      ∃ cs : List (Factor n), (∀ c ∈ cs, c.2.1 ∈ rs) ∧ mk (cs.flatMap conjugateWord) = y
    have prepend (g : FreeGroup (Fin n)) (hg : g ∈ s) (y : FreeGroup (Fin n))
        (hy : P y) (b : Bool) : P (cond b g g⁻¹ * y) := by
      obtain ⟨_, ⟨r, hr, rfl⟩, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hg
      obtain ⟨c, rfl⟩ := isConj_iff.mp hconj
      obtain ⟨cs, hcs, hprod⟩ := hy
      refine ⟨(c.toWord, r, b) :: cs, by simpa using And.intro hr hcs, ?_⟩
      rw [List.flatMap_cons, ← mul_mk, mk_conjugateWord, mk_toWord, hprod]
      cases b
      · simp only [Bool.cond_false, mul_inv_rev, inv_inv, mul_assoc]
      · rfl
    refine Subgroup.closure_induction_left (p := fun y _ => P y) ?_ ?_ ?_ hx
    · exact ⟨[], by simp, rfl⟩
    · exact fun g hg y _ ih => prepend g hg y ih true
    · exact fun g hg y _ ih => prepend g hg y ih false
  · rintro ⟨cs, hcs, rfl⟩
    induction cs with
    | nil => exact one_mem _
    | cons c cs ih =>
      obtain ⟨c, r, b⟩ := c
      rw [List.flatMap_cons, ← mul_mk, mk_conjugateWord]
      have hr : mk r ∈ Subgroup.normalClosure (relatorSet rs) :=
        Subgroup.subset_normalClosure ⟨r, hcs (c, r, b) (List.mem_cons_self), rfl⟩
      have hsign : cond b (mk r) (mk r)⁻¹ ∈ Subgroup.normalClosure (relatorSet rs) := by
        cases b
        · exact inv_mem hr
        · exact hr
      exact mul_mem (Subgroup.Normal.conj_mem _ hsign (mk c)) (ih fun d hd =>
        hcs d (List.mem_cons_of_mem _ hd))

private theorem rePred_mem_normalClosure {n : ℕ} :
    REPred (fun p : List (Word n) × Word n =>
      mk p.2 ∈ Subgroup.normalClosure (relatorSet p.1)) := by
  have hmem : PrimrecRel (fun (c : Factor n) (rs : List (Word n)) => c.2.1 ∈ rs) := by
    have heq : PrimrecRel (fun (r : Word n) (c : Factor n) => r = c.2.1) :=
      Primrec.eq.comp Primrec.fst (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
    exact heq.exists_mem_list.swap.of_eq fun c rs => by simp
  have hprod : Primrec (fun cs : List (Factor n) => reduce (cs.flatMap conjugateWord)) :=
    primrec_reduce.comp
      (Primrec.list_flatMap Primrec.id (primrec_conjugateWord.comp₂ Primrec₂.right))
  let check (p : List (Word n) × Word n) (cs : List (Factor n)) : Prop :=
    (∀ c ∈ cs, c.2.1 ∈ p.1) ∧ reduce (cs.flatMap conjugateWord) = reduce p.2
  have hcheck : PrimrecRel check :=
    (hmem.forall_mem_list.comp Primrec.snd (Primrec.fst.comp Primrec.fst)).and
      (Primrec.eq.comp (hprod.comp Primrec.snd)
        (primrec_reduce.comp (Primrec.snd.comp Primrec.fst)))
  refine (MetaMathlibExt.REPred.exists (R := check) hcheck.computablePred.to_re).of_eq fun p => ?_
  simp only [mem_normalClosure_iff]
  exact exists_congr fun _ => and_congr_right fun _ => ⟨reduce.exact, reduce.sound⟩

private theorem relatorSet_cons {n : ℕ} (w : Word n) (rs : List (Word n)) :
    relatorSet (w :: rs) = insert (mk w) (relatorSet rs) := by
  ext x
  simp [relatorSet, List.mem_cons, or_and_right, exists_or, eq_comm]

-- Choose a representative in the ambient generators for each signed input letter.
private theorem exists_word_substitution {G K : Type*} [Group G] [Group K] {m n : ℕ}
    (π : FreeGroup (Fin m) →* K) (hπ : Function.Surjective π)
    (φ : FreeGroup (Fin n) →* G) (i : G →* K) :
    ∃ t : Word n → Word m, Primrec t ∧ ∀ w, π (mk (t w)) = i (φ (mk w)) := by
  choose rep hrep using fun a : Fin n × Bool => hπ (i (φ (mk [a])))
  let letter (a : Fin n × Bool) := (rep a).toWord
  refine ⟨fun w => w.flatMap letter,
    Primrec.list_flatMap Primrec.id ((Primrec.dom_finite letter).comp₂ Primrec₂.right), ?_⟩
  intro w
  change π (mk (w.flatMap letter)) = i (φ (mk w))
  induction w with
  | nil => simp [← one_eq_mk]
  | cons a w ih =>
    rw [List.flatMap_cons, ← mul_mk, π.map_mul, show a :: w = [a] ++ w from rfl,
      ← mul_mk, φ.map_mul, i.map_mul, ih]
    simp only [letter, mk_toWord, hrep]

-- Imposing x = 1 kills the fixed nonidentity element a exactly when x was nontrivial in H.
private theorem mem_augmented_relators_iff {H K : Type*} [Group H] [Group K] [IsSimpleGroup H]
    {m : ℕ} (π : FreeGroup (Fin m) →* K) (hπ : Function.Surjective π)
    (S : Set (FreeGroup (Fin m))) (hS : Subgroup.normalClosure S = π.ker)
    (g : H →* K) (hg : Function.Injective g) {a x : H} (ha : a ≠ 1)
    {v u : FreeGroup (Fin m)} (hv : π v = g a) (hu : π u = g x) :
    v ∈ Subgroup.normalClosure (insert u S) ↔ x ≠ 1 := by
  let N := Subgroup.normalClosure (insert u S)
  have hker : π.ker ≤ N := hS ▸ Subgroup.normalClosure_mono (Set.subset_insert _ _)
  constructor
  · rintro hmem rfl
    have hN : N ≤ π.ker := Subgroup.normalClosure_le_normal (Set.insert_subset_iff.mpr
      ⟨MonoidHom.mem_ker.mpr (hu.trans (map_one g)), hS ▸ Subgroup.subset_normalClosure⟩)
    apply ha
    apply (map_eq_one_iff g hg).mp
    exact hv ▸ MonoidHom.mem_ker.mp (hN hmem)
  · intro hx
    have : (N.map π).Normal := Subgroup.Normal.map inferInstance π hπ
    have hxmem : x ∈ (N.map π).comap g :=
      ⟨u, Subgroup.subset_normalClosure (Set.mem_insert _ _), hu⟩
    rcases Subgroup.Normal.eq_bot_or_eq_top ((N.map π).comap g) with hb | ht
    · exact (hx (Subgroup.mem_bot.mp (hb ▸ hxmem))).elim
    · have hamem : a ∈ (N.map π).comap g := ht ▸ Subgroup.mem_top a
      change v ∈ N
      rw [← Subgroup.comap_map_eq_self hker]
      exact show π v ∈ N.map π from hv ▸ hamem

set_option linter.dupNamespace false in
set_option linter.unusedVariables false in
/-- **Boone–Higman theorem (easy direction).** Let $\varphi \colon F_n \to G$ be a surjective
homomorphism from the free group $F_n$ on $n$ generators onto a group $G$. If there are injective
homomorphisms $G \to H$ and $H \to K$, where $H$ is a simple group and $K$ is a finitely presented
group, then the word problem of $G$ with respect to $\varphi$ is solvable.

Source: W. W. Boone & G. Higman, *An algebraic characterization of groups with soluble word
problem*, J. Austral. Math. Soc. 18 (1974). Knill, *Some fundamental theorems in mathematics*,
§122. Via leanprover/lean-eval@38361be, problem `boone_higman_embedding`. -/
theorem boone_higman_embedding
    {G H K : Type*} [Group G] [Group H] [Group K]
    [IsSimpleGroup H] [Group.IsFinitelyPresented K]
    (f : G →* H) (hf : Function.Injective f)
    (g : H →* K) (hg : Function.Injective g)
    {n : ℕ} (φ : FreeGroup (Fin n) →* G)
    (hsurj : Function.Surjective φ)
    : WordProblemSolvable φ := by
  classical
  obtain ⟨m, π, hπ, S, hfin, hS⟩ := Group.IsFinitelyPresented.out (G := K)
  let rs := hfin.toFinset.toList.map FreeGroup.toWord
  have hrs : relatorSet rs = S := by
    ext x
    simp [rs, relatorSet, mk_toWord]
  obtain ⟨t, ht, heval⟩ := exists_word_substitution π hπ φ (g.comp f)
  obtain ⟨a, ha⟩ := exists_ne (1 : H)
  obtain ⟨v, hv⟩ := hπ (g a)
  -- Search first for a proof that the translated word follows from the ambient relators.
  -- In parallel, add the word as a relator and search for a proof that it kills a.
  apply ComputablePred.computable_iff_re_compl_re'.2
  constructor
  · refine REPred.of_eq (Partrec.comp (g := fun w => (rs, t w)) rePred_mem_normalClosure
      ((Primrec.const rs).pair ht).to_comp) fun w => ?_
    change mk (t w) ∈ Subgroup.normalClosure (relatorSet rs) ↔ _
    rw [hrs, hS, MonoidHom.mem_ker, heval, map_eq_one_iff (g.comp f) (hg.comp hf)]
  · refine REPred.of_eq (Partrec.comp (g := fun w => (t w :: rs, v.toWord)) rePred_mem_normalClosure
      ((Primrec.list_cons.comp ht (Primrec.const rs)).pair (Primrec.const v.toWord)).to_comp)
      fun w => ?_
    change mk v.toWord ∈ Subgroup.normalClosure (relatorSet (t w :: rs)) ↔ _
    rw [relatorSet_cons, hrs, mk_toWord,
      mem_augmented_relators_iff π hπ S hS g hg ha hv (heval w)]
    exact map_ne_one_iff f hf

end MathlibExt.GroupTheory.BooneHigmanEmbeddingWanted.GroupTheory.BooneHigmanEmbedding
