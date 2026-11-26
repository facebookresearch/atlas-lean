/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Databases.RelationalCalculus.SafeRange

/-!
# Domain independence from local range restriction

Following the domain-independence clause of Abiteboul, Hull and Vianu, *Foundations of
Databases*, Theorem 5.4.6 (p. 86), we prove soundness for the specific syntactic test
`Formula.SafeRange`. Its equality propagation is local to each flattened conjunction and its
quantifier checks use no guards from outside the quantified body.

The proof does not translate through relational algebra. A satisfying assignment takes the
variables certified by the checker into the active domain. Changing the underlying domain cannot
change truth: every successful existential witness lies in the common active domain. The same
bound on the free variables then transports the whole valuation. This implication holds for
every accepted query; the converse is not required.
-/

public section

namespace Cslib.Databases.RelationalCalculus

variable {N A D : Type*} {S : N → Finset A} {n k : ℕ}

private def AllIn (s : Finset (Fin n)) (P : Fin n → Prop) := ∀ i ∈ s, P i

private def Respects (r : RangeInfo n) (P : Fin n → Prop) :=
  AllIn r.seeds P ∧ ∀ f ∈ r.rules, AllIn f.lhs P → AllIn f.rhs P

private theorem propagate {F : Finset (FD (Fin n))} {P : Fin n → Prop}
    (hF : ∀ f ∈ F, AllIn f.lhs P → AllIn f.rhs P) {f : FD (Fin n)} (h : Derives F f) :
    AllIn f.lhs P → AllIn f.rhs P := by
  induction h with
  | mem h => exact hF _ h
  | refl h => exact fun hs i hi => hs i (h hi)
  | augment Z h ih =>
    intro hs i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact ih (fun j hj => hs j (Finset.mem_union_left _ hj)) i hi
    · exact hs i (Finset.mem_union_right _ hi)
  | trans _ _ ih jh => exact jh ∘ ih

private theorem respects_bounds {r : RangeInfo n} {P : Fin n → Prop} (h : Respects r P) :
    AllIn r.bounds P := propagate h.2 (derives_attrClosure r.rules r.seeds) h.1

private theorem respects_merge {r s : RangeInfo n} {P : Fin n → Prop}
    (h : Respects r P) (j : Respects s P) : Respects (r.merge s) P := by
  constructor
  · exact fun i hi => (Finset.mem_union.mp hi).elim (h.1 i) (j.1 i)
  · exact fun f hf => (Finset.mem_union.mp hf).elim (h.2 f) (j.2 f)

private theorem respects_seed {s : Finset (Fin n)} {P : Fin n → Prop} (ok : Bool)
    (h : AllIn s P) : Respects { seeds := s, ok := ok } P := ⟨h, by simp⟩

variable [Fintype N] {I : Instance S D} {B : Set D}

/-- Local invariant, even when some free values are outside both underlying domains. -/
private theorem sat_respects (hI : ↑I.values ⊆ B) (d : Set D) (p : Formula S D n)
    (hc : ↑p.constants ⊆ B) (v : Fin n → D) (hs : p.Sat I d v) :
    Respects p.scan (fun i => v i ∈ B) := by
  classical
  induction p with
  | rel r ts =>
    obtain ⟨t, ht, hts⟩ := hs
    apply respects_seed
    intro i hi
    obtain ⟨a, _, ha⟩ := Finset.mem_biUnion.mp hi
    specialize hts a
    cases e : ts a with
    | var j =>
      simp only [e, Term.vars, Finset.mem_singleton] at ha
      subst j
      exact hI (I.mem_values.mpr ⟨r, t, ht, a, by simpa [e, Term.eval] using hts⟩)
    | const c => simp [e, Term.vars] at ha
  | eq s t =>
    cases s <;> cases t <;>
      simp_all [Respects, AllIn, Formula.scan, RangeInfo.ofEq, Formula.Sat, Term.eval,
        Formula.constants, Term.constants]
  | conj p q ih jh =>
    simp only [Formula.constants, Finset.coe_union, Set.union_subset_iff] at hc
    exact respects_merge (ih hc.1 _ hs.1) (jh hc.2 _ hs.2)
  | disj p q ih jh =>
    simp only [Formula.constants, Finset.coe_union, Set.union_subset_iff] at hc
    apply respects_seed
    intro i hi
    exact hs.elim (fun h => respects_bounds (ih hc.1 _ h) i (Finset.mem_inter.mp hi).1)
      (fun h => respects_bounds (jh hc.2 _ h) i (Finset.mem_inter.mp hi).2)
  | ex p ih =>
    obtain ⟨x, _, h⟩ := hs
    apply respects_seed
    intro i hi
    have hj := (Finset.mem_filter.mp hi).2
    simpa using respects_bounds (ih hc _ h) i.castSucc hj
  | neg | all => apply respects_seed; simp [AllIn]

/-- A successful analysis certifies stability of truth on each assignment, even before the final
check on free variables. -/
private theorem sat_congr (hI : ↑I.values ⊆ B) {d e : Set D} (hd : B ⊆ d) (he : B ⊆ e)
    (p : Formula S D n) (hc : ↑p.constants ⊆ B) (ok : p.scan.ok = true) (v : Fin n → D) :
    p.Sat I d v ↔ p.Sat I e v := by
  induction p with
  | eq | rel => rfl
  | conj p q ih jh | disj p q ih jh =>
    simp only [Formula.constants, Finset.coe_union, Set.union_subset_iff] at hc
    replace ok := Bool.and_eq_true_iff.mp ok
    simp only [Formula.Sat, ih hc.1 ok.1, jh hc.2 ok.2]
  | neg p ih => exact not_congr (ih hc ok v)
  | all p ih => contradiction
  | ex p ih =>
    obtain ⟨hp, hb⟩ := Bool.and_eq_true_iff.mp ok
    have hb' := of_decide_eq_true hb
    have bound (d : Set D) (x : D) (h : p.Sat I d (Fin.snoc v x)) : x ∈ B := by
      simpa using respects_bounds (sat_respects hI d p hc _ h) _ hb'
    constructor
    · rintro ⟨x, _, h⟩
      exact ⟨x, he (bound d x h), (ih hc hp _).mp h⟩
    · rintro ⟨x, _, h⟩
      exact ⟨x, hd (bound e x h), (ih hc hp _).mpr h⟩

/-- Every query accepted by the local `Formula.SafeRange` test is domain independent: for each
finite input instance, its images coincide for all choices of underlying domain. This gives the
domain-independence implication of AHV Theorem 5.4.6 for this specific range analysis. -/
theorem Query.domainIndependent_of_safeRange (q : Query S D n k) (h : q.body.SafeRange) :
    q.DomainIndependent := by
  classical
  apply q.domainIndependent_iff.mpr
  intro I d e hd he
  let p := q.body.pushNeg false
  change (if p.scan.ok then some p.scan.bounds else none) = some q.body.vars at h
  split at h <;> rename_i ok
  · have hr : p.scan.bounds = Finset.univ := (Option.some.inj h).trans q.body_vars
    have hI : ↑I.values ⊆ (q.activeDomain I : Set D) := by
      simp [Query.activeDomain]
    have hc : ↑p.constants ⊆ (q.activeDomain I : Set D) := by
      simp only [p, Formula.constants_pushNeg, Query.activeDomain, Finset.coe_union]
      exact fun _ hx => Or.inl (Or.inr hx)
    have norm (d : Set D) (v : Fin n → D) : p.Sat I d v ↔ q.body.Sat I d v := by
      simpa [p] using q.body.sat_pushNeg I d false v
    have hb (d : Set D) (v : Fin n → D) (hs : p.Sat I d v) : ∀ i, v i ∈ q.activeDomain I :=
      fun i => respects_bounds (sat_respects hI d p hc v hs) i (by rw [hr]; exact Finset.mem_univ i)
    ext t
    constructor
    · rintro ⟨v, _, hs, rfl⟩
      have hp := (norm d v).mpr hs
      exact ⟨v, fun i => he (hb d v hp i),
        (norm e v).mp ((sat_congr hI hd he p hc ok v).mp hp), rfl⟩
    · rintro ⟨v, _, hs, rfl⟩
      have hp := (norm e v).mpr hs
      exact ⟨v, fun i => hd (hb e v hp i),
        (norm d v).mp ((sat_congr hI hd he p hc ok v).mpr hp), rfl⟩
  · contradiction

end Cslib.Databases.RelationalCalculus
