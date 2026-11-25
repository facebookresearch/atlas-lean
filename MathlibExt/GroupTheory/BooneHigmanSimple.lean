/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/GroupTheory/BooneHigmanSimple.lean` (leanprover/lean-eval, commit
38361be884302c7edce1908c4aef8296eb2cb27e), for the statement of Kuznetsov's theorem.
Copyright 2026 Lean FRO, LLC.
Author (benchmark submitter): Kim Morrison.
The ATLAS adaptation uses a regular theorem with a proof and keeps the wanted statement.
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
# Kuznetsov's theorem on finitely presented simple groups

`boone_higman_simple` proves that every finite presentation of a simple group has a solvable
word problem. The two searches enumerate normal-closure certificates for the original relators
and for the relators augmented by the input word.
-/

public section

open MathlibExt.GroupTheory.WordProblemSolvableShared

namespace MathlibExt.GroupTheory.BooneHigmanSimpleWanted.GroupTheory.BooneHigmanSimpleProblem

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

set_option linter.dupNamespace false in
/-- **Kuznetsov's theorem on finitely presented simple groups.** Let $G$ be a simple group, let
$F_n$ be the free group on $n$ generators, and let $\varphi \colon F_n \to G$ be a surjective
homomorphism whose kernel is the normal closure of finitely many elements. Then the word problem
of $G$ with respect to $\varphi$ is solvable: there is an algorithm that decides, for every word
$w$ in the $n$ generators and their inverses, whether $\varphi(w) = 1$.

Source: A.V. Kuznetsov, 'Algorithms as operations in algebraic systems', Uspekhi Mat. Nauk 13 (1958)
240–241 (Russian); W.W. Boone and G. Higman, 'An algebraic characterization of groups with soluble
word problem', J. Austral. Math. Soc. 18 (1974) 41–53. §122 in O. Knill, *Some Fundamental Theorems
in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via
leanprover/lean-eval@38361be, problem `boone_higman_simple`. -/
theorem boone_higman_simple
    {G : Type*} [Group G] [IsSimpleGroup G]
    {n : ℕ} (φ : FreeGroup (Fin n) →* G)
    (_hsurj : Function.Surjective φ)
    (_hker : (MonoidHom.ker φ).IsFinitelyNormallyGenerated) :
    WordProblemSolvable φ := by
  classical
  obtain ⟨S, hSfinite, hSker⟩ := _hker
  let rs := hSfinite.toFinset.toList.map FreeGroup.toWord
  have hrs : relatorSet rs = S := by
    ext g
    simp [rs, relatorSet, mk_toWord]
  obtain ⟨a, ha⟩ := exists_ne (1 : G)
  obtain ⟨g, hg⟩ := _hsurj a
  let v := g.toWord
  have hv : φ (mk v) ≠ 1 := by simpa [v, mk_toWord, hg] using ha
  -- Adding a word that is already trivial leaves the kernel unchanged.
  -- Adding a nontrivial word makes the normal closure surject onto the simple group.
  have hneg (w : Word n) :
      mk v ∈ Subgroup.normalClosure (relatorSet (w :: rs)) ↔ φ (mk w) ≠ 1 := by
    rw [relatorSet_cons, hrs]
    let N := Subgroup.normalClosure (insert (mk w) S)
    have hkerN : φ.ker ≤ N :=
      hSker ▸ Subgroup.normalClosure_mono (Set.subset_insert _ _)
    constructor
    · intro hmem h
      have hN : N ≤ φ.ker :=
        Subgroup.normalClosure_le_normal (Set.insert_subset_iff.mpr
          ⟨MonoidHom.mem_ker.mpr h, hSker ▸ Subgroup.subset_normalClosure⟩)
      exact hv (MonoidHom.mem_ker.mp (hN hmem))
    · intro h
      have : (N.map φ).Normal := Subgroup.Normal.map inferInstance φ _hsurj
      have hw : φ (mk w) ∈ N.map φ :=
        ⟨mk w, Subgroup.subset_normalClosure (Set.mem_insert _ _), rfl⟩
      have htop : N.map φ = ⊤ := by
        rcases Subgroup.Normal.eq_bot_or_eq_top (N.map φ) with hb | ht
        · exact (h (Subgroup.mem_bot.mp (hb ▸ hw))).elim
        · exact ht
      have hN : N = ⊤ := by
        rw [← Subgroup.comap_map_eq_self hkerN, htop, Subgroup.comap_top]
      change mk v ∈ N
      rw [hN]
      exact Subgroup.mem_top (mk v)
  apply ComputablePred.computable_iff_re_compl_re'.2
  constructor
  · refine REPred.of_eq (p := fun w : Word n =>
      mk w ∈ Subgroup.normalClosure (relatorSet rs))
      (Partrec.comp (g := fun w : Word n => (rs, w)) rePred_mem_normalClosure
        ((Primrec.const rs).pair Primrec.id).to_comp) fun w => ?_
    rw [hrs, hSker, MonoidHom.mem_ker]
  · refine REPred.of_eq ?_ hneg
    exact Partrec.comp (g := fun w : Word n => (w :: rs, v)) rePred_mem_normalClosure
      ((Primrec.list_cons.comp Primrec.id (Primrec.const rs)).pair (Primrec.const v)).to_comp

end MathlibExt.GroupTheory.BooneHigmanSimpleWanted.GroupTheory.BooneHigmanSimpleProblem
