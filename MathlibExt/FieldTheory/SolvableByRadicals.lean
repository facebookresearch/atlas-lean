/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Attribution for the theorem statement

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Attribution and modification notice (Apache License 2.0, Section 4):
taken from leanprover/lean-eval at commit
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Algebra.SolvableByRadicals` —
solvable_by_radicals_converse (manifest
`manifests/problems/solvable_by_radicals_converse.toml`, rev 1, submitter Kim Morrison,
status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Algebra.SolvableByRadicalsWanted` namespace.
Mathematical statements are unchanged. ATLAS subsequently proved the criterion and
moved it to the proved library, retaining the original declaration name.
Source: É. Galois (1832); the iff appears in standard texts such as Stewart, *Galois Theory*
(Theorem 18.10); Lang, *Algebra* (VI §7); Rotman, *Galois Theory* (Theorem 73).
Listed as §58 (additional statement 2) in O. Knill, *Some Fundamental Theorems in Mathematics*
(https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf).
-/

module

public import Mathlib.FieldTheory.AbelRuffini
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.KummerExtension

/-!
# Solvability by radicals and solvable Galois groups

The forward implication applies Mathlib's Abel–Ruffini theorem to each irreducible factor.
For the converse, adjoin a primitive root of unity of order `Nat.card p.Gal`, then use the
Galois correspondence and Kummer theory to build a tower of cyclic extensions. The degrees
of the cyclic steps divide `Nat.card p.Gal`, so the base supplies the roots of unity needed
at every step.
-/

open Polynomial IntermediateField

private theorem gal_isSolvable_of_roots_radical {F : Type*} [Field F]
    {p : F[X]} (hp : p ≠ 0)
    (h : ∀ x : AlgebraicClosure F, aeval x p = 0 → x ∈ solvableByRad F (AlgebraicClosure F)) :
    Group.IsSolvable p.Gal := by
  classical
  obtain ⟨s, hs, hassoc⟩ := UniqueFactorizationMonoid.exists_prime_factors p hp
  have hprod : Group.IsSolvable s.prod.Gal := gal_prod_isSolvable fun q hq => by
    have hqi := (hs q hq).irreducible
    obtain ⟨x, hx⟩ :=
      IsAlgClosed.exists_aeval_eq_zero (AlgebraicClosure F) q hqi.degree_pos.ne'
    obtain ⟨r, hr⟩ := (Multiset.dvd_prod hq).trans hassoc.dvd
    have hxp : aeval x p = 0 := by rw [hr, map_mul, hx, zero_mul]
    exact isSolvable_gal_of_irreducible (h x hxp) hqi hx
  exact Group.isSolvable_of_surjective
    (Polynomial.Gal.restrictDvd_surjective hassoc.symm.dvd (hassoc.ne_zero_iff.mpr hp))

private theorem exists_cyclic_quotient (G : Type*) [Group G] [Finite G]
    [Nontrivial G] [Group.IsSolvable G] :
    ∃ (N : Subgroup G) (_ : N.Normal), N ≠ ⊤ ∧ IsCyclic (G ⧸ N) := by
  classical
  -- A maximal subgroup above the commutator is normal, with a simple cyclic quotient.
  obtain ⟨N, hN, hle⟩ :=
    (eq_top_or_exists_le_coatom (commutator G)).resolve_left
      (Group.IsSolvable.commutator_lt_top_of_nontrivial (G := G)).ne
  have hnormal : N.Normal := Subgroup.Normal.of_commutator_le G hle
  let e := QuotientGroup.comapMk'OrderIso N
  have hquot (H : Subgroup (G ⧸ N)) : H = ⊥ ∨ H = ⊤ := by
    rcases eq_or_lt_of_le (show N ≤ (e H).1 from (e H).2) with h | h
    · left
      apply e.injective
      rw [e.map_bot]
      exact Subtype.ext h.symm
    · right
      apply e.injective
      rw [e.map_top]
      exact Subtype.ext (hN.2 _ h)
  have : Nontrivial (G ⧸ N) := not_subsingleton_iff_nontrivial.mp fun h =>
    hN.1 (QuotientGroup.subgroup_eq_top_of_subsingleton N h)
  obtain ⟨g, hg⟩ := exists_ne (1 : G ⧸ N)
  exact ⟨N, hnormal, hN.1, isCyclic_iff_exists_zpowers_eq_top.mpr
    ⟨g, (hquot (Subgroup.zpowers g)).resolve_left (Subgroup.zpowers_ne_bot.mpr hg)⟩⟩

-- Grow the part of the extension already contained in `R` by one cyclic factor at a time.
private theorem eq_top_of_radical_closed {K E : Type*} [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] [IsGalois K E] [Group.IsSolvable Gal(E/K)]
    {n : ℕ} {ζ : K} (hn : n ≠ 0) (hζ : IsPrimitiveRoot ζ n) (hdvd : Module.finrank K E ∣ n)
    (R : IntermediateField K E) (hrad : ∀ x : E, ∀ d ≠ 0, x ^ d ∈ R → x ∈ R) : R = ⊤ := by
  suffices ∀ S : IntermediateField K E, S ≤ R → R = ⊤ from this ⊥ bot_le
  intro S
  induction S using (measure fun T : IntermediateField K E => Module.finrank T E).wf.induction with
  | h S ih =>
    intro hSR
    by_cases hS : S = ⊤
    · exact top_le_iff.mp (hS ▸ hSR)
    have hnontrivial : Nontrivial Gal(E/S) := by
      rw [← not_subsingleton_iff_nontrivial]
      intro hs
      apply hS
      have : Subsingleton S.fixingSubgroup := S.fixingSubgroupEquiv.injective.subsingleton
      have hbot : S.fixingSubgroup = ⊥ := by
        apply le_antisymm _ bot_le
        intro g hg
        exact Subgroup.mem_bot.mpr
          (congrArg Subtype.val (Subsingleton.elim (⟨g, hg⟩ : S.fixingSubgroup) 1))
      rw [← IsGalois.fixedField_fixingSubgroup S, hbot, IntermediateField.fixedField_bot]
    have : Group.IsSolvable Gal(E/S) :=
      Group.isSolvable_of_surjective (f := S.fixingSubgroupEquiv.toMonoidHom)
        S.fixingSubgroupEquiv.surjective
    obtain ⟨N, hnormal, hN, hcyc⟩ := exists_cyclic_quotient Gal(E/S)
    let C := IntermediateField.fixedField N
    have hC : C ≠ ⊥ := by
      intro h
      apply hN
      rw [← IntermediateField.fixingSubgroup_fixedField N, ← show C = fixedField N from rfl,
        h, IntermediateField.fixingSubgroup_bot]
    have : IsCyclic Gal(C/S) := (IsGalois.normalAutEquivQuotient N).isCyclic.mp hcyc
    have hd : Module.finrank S C ≠ 0 := Module.finrank_pos.ne'
    have hdn : Module.finrank S C ∣ n := (Module.finrank_dvd_finrank_right S C E).trans
      ((Module.finrank_dvd_finrank_left K S E).trans hdvd)
    have hprim : (primitiveRoots (Module.finrank S C) S).Nonempty := by
      obtain ⟨m, hm⟩ := hdn
      have hζ' := (IsPrimitiveRoot.pow (Nat.pos_of_ne_zero hn) hζ
        (hm.trans (Nat.mul_comm _ _))).map_of_injective (algebraMap K S).injective
      exact ⟨_, (mem_primitiveRoots (Nat.pos_of_ne_zero hd)).mpr hζ'⟩
    obtain ⟨α, ⟨a, ha⟩, hgen⟩ := exists_root_adjoin_eq_top_of_isCyclic S C hprim
    have haE : (a : E) = (α : E) ^ Module.finrank S C := congrArg C.val ha
    have hα : (α : E) ∈ R := hrad _ _ hd (haE ▸ hSR a.2)
    let R' : IntermediateField S E := IntermediateField.extendScalars hSR
    have hCR : C ≤ R' := by
      have hle : S⟮α⟯ ≤ R'.comap C.val :=
        adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hα)
      rw [hgen, top_le_iff] at hle
      exact fun x hx => show (⟨x, hx⟩ : C) ∈ R'.comap C.val from hle.symm ▸ mem_top
    let T := C.restrictScalars K
    have hST : S ≤ T := fun x hx => C.algebraMap_mem (⟨x, hx⟩ : S)
    have hST' : S < T := lt_of_le_of_ne hST fun heq => hC <| eq_bot_iff.mpr fun x hx =>
      mem_bot.mpr ⟨⟨x, heq.symm ▸ (show x ∈ T from hx)⟩, rfl⟩
    exact ih T (IntermediateField.finrank_lt_of_gt hST') hCR

-- The roots of `X ^ n - 1` are distinct in characteristic zero, so the
-- group of `n`-th roots of unity has order `n`.
private theorem exists_primitive_root {L : Type*} [Field L] [CharZero L] [IsAlgClosed L]
    (n : ℕ) [NeZero n] : ∃ ζ : L, IsPrimitiveRoot ζ n := by
  classical
  rw [← card_rootsOfUnity_eq_iff_exists_isPrimitiveRoot,
    Nat.card_congr (rootsOfUnityEquivNthRoots L n), Nat.card_eq_fintype_card]
  change ((nthRoots n (1 : L)).attach.dedup).card = n
  have hs : (X ^ n - C (1 : L)).Separable :=
    separable_X_pow_sub_C 1 (Nat.cast_ne_zero.mpr (NeZero.ne n)) one_ne_zero
  have hroots : (nthRoots n (1 : L)).Nodup := Polynomial.nodup_roots hs
  rw [Multiset.dedup_eq_self.mpr (Multiset.nodup_attach.mpr hroots), Multiset.card_attach]
  change (X ^ n - C (1 : L)).roots.card = n
  rw [← (IsAlgClosed.splits _).natDegree_eq_card_roots]
  exact natDegree_X_pow_sub_C (1 : L)

private theorem roots_radical_of_gal_isSolvable {F : Type*} [Field F] [CharZero F]
    (p : F[X]) (hp : p ≠ 0) [Group.IsSolvable p.Gal] :
    ∀ x : AlgebraicClosure F, aeval x p = 0 → x ∈ solvableByRad F (AlgebraicClosure F) := by
  classical
  let Ω := AlgebraicClosure F
  let R := solvableByRad F Ω
  let n := Nat.card p.Gal
  have hn : n ≠ 0 := Nat.card_pos.ne'
  have : NeZero n := ⟨hn⟩
  obtain ⟨ζ, hζ⟩ := exists_primitive_root (L := Ω) n
  have hζR : ζ ∈ R := solvableByRad.rad_mem hn (hζ.pow_eq_one ▸ R.one_mem)
  let K := F⟮ζ⟯
  have hKR : K ≤ R := adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hζR)
  have hζK : IsPrimitiveRoot (⟨ζ, mem_adjoin_simple_self F ζ⟩ : K) n :=
    IsPrimitiveRoot.of_map_of_injective (f := K.val) hζ K.val.injective
  let q := p.map (algebraMap F K)
  let E := q.SplittingField
  have hsplitQ : (q.map (algebraMap K E)).Splits := SplittingField.splits q
  have : Fact ((p.map (algebraMap F E)).Splits) :=
    ⟨by rwa [IsScalarTower.algebraMap_eq F K E, ← Polynomial.map_map]⟩
  have : IsGalois K E := isGalois_iff.mpr ⟨inferInstance, inferInstance⟩
  -- An automorphism over `K` is determined by what it does to the roots of `p`.
  let restrictF := MulSemiringAction.toAlgAut Gal(E/K) F E
  let g := (Polynomial.Gal.restrict p E).comp restrictF
  have hinj : Function.Injective g := by
    intro σ τ h
    apply Polynomial.Gal.ext q
    intro x hx
    rw [rootSet_map] at hx
    have act (u : Gal(E/K)) := Polynomial.Gal.restrict_smul (restrictF u) ⟨x, hx⟩
    change Polynomial.Gal.restrict p E (restrictF σ) =
      Polynomial.Gal.restrict p E (restrictF τ) at h
    exact (act σ).symm.trans (h ▸ act τ)
  have : Group.IsSolvable Gal(E/K) := Group.isSolvable_of_isSolvable_injective hinj
  have hd : Module.finrank K E ∣ n := by
    rw [← IsGalois.card_aut_eq_finrank]
    exact Subgroup.card_dvd_of_injective g hinj
  let f : E →ₐ[K] Ω := SplittingField.lift q (IsAlgClosed.splits _)
  let R' : IntermediateField K E := (IntermediateField.extendScalars hKR).comap f
  have hR' : R' = ⊤ := eq_top_of_radical_closed hn hζK hd R' fun x d hd hx =>
    show f x ∈ R from solvableByRad.rad_mem hd (by rw [← map_pow]; exact hx)
  intro x hx
  have hxq : x ∈ q.rootSet Ω := by
    rw [rootSet_map]
    exact (mem_rootSet_of_ne hp).mpr hx
  rw [← hsplitQ.image_rootSet f] at hxq
  obtain ⟨y, _, rfl⟩ := hxq
  exact show y ∈ R' from hR'.symm ▸ mem_top

@[expose] public section

namespace MathlibExt.Algebra.SolvableByRadicalsWanted.Algebra

-- Keep the original public name, including both `Algebra` components.
set_option linter.dupNamespace false in
/-- **Solvable extensions ↔ solvable groups.** Let $F$ be a field of characteristic zero and let
$p \in F[X]$ be a nonzero polynomial. Every root of $p$ in an algebraic closure $\overline{F}$ of
$F$ is solvable by radicals over $F$ (obtainable from $F$ by field operations and $n$-th roots
inside $\overline{F}$) if and only if the Galois group of $p$ over $F$ is solvable.

Source: É. Galois (1832); the iff appears in standard texts such as Stewart, *Galois Theory* (Theorem 18.10); Lang, *Algebra* (VI §7); Rotman, *Galois Theory* (Theorem 73). Listed as §58 (additional statement 2) in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via leanprover/lean-eval@38361be, problem `solvable_by_radicals_converse`. -/
theorem solvable_iff_solvableByRad (F : Type*) [Field F] [CharZero F]
    (p : F[X]) (_hp : p ≠ 0) :
    (∀ x : AlgebraicClosure F, aeval x p = 0 →
        x ∈ solvableByRad F (AlgebraicClosure F)) ↔ Group.IsSolvable p.Gal :=
  ⟨gal_isSolvable_of_roots_radical _hp, fun _ => roots_radical_of_gal_isSolvable p _hp⟩

end MathlibExt.Algebra.SolvableByRadicalsWanted.Algebra
