/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HOSPITALS/RESIDENTS WITH COUPLES is NP-complete

Source:
E. Ronn, "NP-complete stable matching problems", Journal of Algorithms 11 (1990), 285-304,
doi:10.1016/0196-6774(90)90007-2;
E. J. McDermid and D. F. Manlove, "Keeping partners together: algorithmic results for the
hospitals/residents problem with couples", Journal of Combinatorial Optimization 19 (2010),
279-303, doi:10.1007/s10878-009-9257-2;
P. Biró, D. F. Manlove, and I. McBride, "The Hospitals / Residents problem with Couples:
complexity and integer programming models", Experimental Algorithms (SEA 2014), Lecture Notes in
Computer Science 8504, 10-21, doi:10.1007/978-3-319-07959-2_2; extended version
arXiv:1308.4534, Section 1.1.1 and Definition 1 (MM-stability), Section 1.2, Theorem 1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HospitalsResidentsWithCouples

/-!
# HOSPITALS/RESIDENTS WITH COUPLES is NP-complete

INSTANCE (Biró, Manlove and McBride, Section 1.1.1): a set `H` of hospitals and a set `R` of
residents, partitioned into single residents and residents in couples; a set of couples
`(rᵢ, rⱼ)`, each resident in a couple belonging to exactly one couple. Each single resident has a
linear preference order over his acceptable hospitals; each couple `(rᵢ, rⱼ)` has a joint linear
preference order over a set `A ⊆ H × H` of acceptable pairs, `(h_p, h_q)` meaning `rᵢ` at `h_p`
and `rⱼ` at `h_q`; each hospital `hⱼ` has a capacity `cⱼ` and a linear preference order over the
residents who find `hⱼ` acceptable, as single residents or as members of couples.
A matching assigns residents to hospitals such that each single resident is unassigned or
assigned to an acceptable hospital, each couple is jointly unassigned or jointly assigned to an
acceptable pair, and no hospital exceeds its capacity.
QUESTION: is there an MM-stable matching (Definition 1, McDermid and Manlove's stability)?

Deciding whether a stable matching exists is NP-complete even with no single residents and all
capacities `1` (Ronn 1990, as recorded by Biró, Manlove and McBride, Section 1.2; their Theorem 1
proves it again for MM-stability with preference lists of length at most 2), and checking that a
matching is MM-stable takes polynomial time. With all capacities `1`, MM-stability is the
stability of Gusfield and Irving (Section 1.1.1).

Hospitals are `0, …, |H| - 1` in the order listed; residents are natural numbers; preference
lists are lists, most preferred first. A matching is a map from residents to `Option` hospitals
(`none`: unassigned). For a couple that is jointly unassigned, every acceptable pair is preferred
to its assignment.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the hospitals `(cⱼ, preference list over residents)`, the single residents
`(rᵢ, preference list over hospitals)`, and the couples `((rᵢ, rⱼ), joint preference list over
hospital pairs)`. -/
abbrev HospitalsResidentsWithCouplesInstance :=
  List (ℕ × List ℕ) × List (ℕ × List ℕ) × List ((ℕ × ℕ) × List (ℕ × ℕ))

/-- `x` is strictly preferred to `y` in the preference list `l` (both listed, `x` first). -/
def Prefers {α : Type} [DecidableEq α] (l : List α) (x y : α) : Prop :=
  x ∈ l ∧ y ∈ l ∧ l.idxOf x < l.idxOf y

/-- The residents of the instance: the single residents, then both members of each couple. -/
def residents (i : HospitalsResidentsWithCouplesInstance) : List ℕ :=
  i.2.1.map Prod.fst ++ i.2.2.flatMap fun c => [c.1.1, c.1.2]

/-- The capacity `cₕ` of hospital `h`. -/
def capacity (i : HospitalsResidentsWithCouplesInstance) (h : ℕ) : ℕ :=
  (i.1.getD h (0, [])).1

/-- The preference list of hospital `h`. -/
def hospitalPrefs (i : HospitalsResidentsWithCouplesInstance) (h : ℕ) : List ℕ :=
  (i.1.getD h (0, [])).2

/-- Well-formedness: positive capacities; preference lists without repetitions, over listed
hospitals; the two members of a couple are distinct and every resident is listed once; and each
hospital ranks exactly the residents who find it acceptable, as single residents or as members
of couples. -/
def WellFormed (i : HospitalsResidentsWithCouplesInstance) : Prop :=
  (∀ h ∈ i.1, 0 < h.1 ∧ h.2.Nodup) ∧
    (∀ s ∈ i.2.1, s.2.Nodup ∧ ∀ h ∈ s.2, h < i.1.length) ∧
    (∀ c ∈ i.2.2, c.1.1 ≠ c.1.2 ∧ c.2.Nodup ∧ ∀ p ∈ c.2, p.1 < i.1.length ∧ p.2 < i.1.length) ∧
    (residents i).Nodup ∧
    (∀ h < i.1.length, ∀ r ∈ hospitalPrefs i h,
      (∃ s ∈ i.2.1, s.1 = r ∧ h ∈ s.2) ∨
        ∃ c ∈ i.2.2, (c.1.1 = r ∧ ∃ p ∈ c.2, p.1 = h) ∨ (c.1.2 = r ∧ ∃ p ∈ c.2, p.2 = h)) ∧
    (∀ s ∈ i.2.1, ∀ h ∈ s.2, s.1 ∈ hospitalPrefs i h) ∧
    ∀ c ∈ i.2.2, ∀ p ∈ c.2, c.1.1 ∈ hospitalPrefs i p.1 ∧ c.1.2 ∈ hospitalPrefs i p.2

/-- `M(h)`: the residents assigned to hospital `h` by `M`. -/
def assigned (i : HospitalsResidentsWithCouplesInstance) (M : ℕ → Option ℕ) (h : ℕ) :
    List ℕ :=
  (residents i).filter fun r => M r = some h

/-- `M` is a matching: single residents are unassigned or at an acceptable hospital, couples are
jointly unassigned or jointly at an acceptable pair, and no hospital exceeds its capacity. -/
def IsMatching (i : HospitalsResidentsWithCouplesInstance) (M : ℕ → Option ℕ) : Prop :=
  (∀ s ∈ i.2.1, match M s.1 with
    | none => True
    | some h => h ∈ s.2) ∧
    (∀ c ∈ i.2.2, (M c.1.1 = none ∧ M c.1.2 = none) ∨
      ∃ p ∈ c.2, M c.1.1 = some p.1 ∧ M c.1.2 = some p.2) ∧
    ∀ h < i.1.length, (assigned i M h).length ≤ capacity i h

/-- Hospital `h` is under-subscribed in `M`. -/
def Undersubscribed (i : HospitalsResidentsWithCouplesInstance) (M : ℕ → Option ℕ) (h : ℕ) :
    Prop :=
  (assigned i M h).length < capacity i h

/-- Hospital `h` prefers resident `r` to some member of `X`. -/
def PrefersToSome (i : HospitalsResidentsWithCouplesInstance) (h r : ℕ) (X : List ℕ) : Prop :=
  ∃ r' ∈ X, Prefers (hospitalPrefs i h) r r'

/-- The couple `c` prefers the pair `p` to its assignment `(M(rᵢ), M(rⱼ))` (every acceptable pair
is preferred to being jointly unassigned). -/
def CouplePrefers (M : ℕ → Option ℕ) (c : (ℕ × ℕ) × List (ℕ × ℕ)) (p : ℕ × ℕ) : Prop :=
  match M c.1.1, M c.1.2 with
  | some a, some b => Prefers c.2 p (a, b)
  | _, _ => p ∈ c.2

/-- Definition 1, case 1: a single resident `rᵢ` and a hospital `hⱼ` block `M`, as in the
classical HR problem: `hⱼ` is acceptable to `rᵢ`, who is unassigned or prefers `hⱼ` to `M(rᵢ)`,
and `hⱼ` is under-subscribed or prefers `rᵢ` to some member of `M(hⱼ)`. -/
def BlockedBySingle (i : HospitalsResidentsWithCouplesInstance) (M : ℕ → Option ℕ) : Prop :=
  ∃ s ∈ i.2.1, ∃ h ∈ s.2,
    (match M s.1 with
      | none => True
      | some h' => Prefers s.2 h h') ∧
    (Undersubscribed i M h ∨ PrefersToSome i h s.1 (assigned i M h))

/-- Definition 1, case 2: a couple `(rᵢ, rⱼ)` and a hospital `hₖ` block `M`: either (a) the
couple prefers `(hₖ, M(rⱼ))` to `(M(rᵢ), M(rⱼ))` and `hₖ` is under-subscribed or prefers `rᵢ` to
some member of `M(hₖ) \ {rⱼ}`, or (b) the couple prefers `(M(rᵢ), hₖ)` to `(M(rᵢ), M(rⱼ))` and
`hₖ` is under-subscribed or prefers `rⱼ` to some member of `M(hₖ) \ {rᵢ}`. The pairs
`(hₖ, M(rⱼ))` and `(M(rᵢ), hₖ)` range over the couple's list. -/
def BlockedByCoupleAndHospital (i : HospitalsResidentsWithCouplesInstance)
    (M : ℕ → Option ℕ) : Prop :=
  ∃ c ∈ i.2.2, match M c.1.1, M c.1.2 with
    | some a, some b =>
      (∃ p ∈ c.2, p.2 = b ∧ Prefers c.2 p (a, b) ∧
        (Undersubscribed i M p.1 ∨
          PrefersToSome i p.1 c.1.1 ((assigned i M p.1).filter (· ≠ c.1.2)))) ∨
      ∃ p ∈ c.2, p.1 = a ∧ Prefers c.2 p (a, b) ∧
        (Undersubscribed i M p.2 ∨
          PrefersToSome i p.2 c.1.2 ((assigned i M p.2).filter (· ≠ c.1.1)))
    | _, _ => False

/-- Definition 1, case 3: a couple `(rᵢ, rⱼ)` and hospitals `hₖ ≠ M(rᵢ)`, `hₗ ≠ M(rⱼ)` (not
necessarily distinct) block `M`: the couple prefers `(hₖ, hₗ)` to `(M(rᵢ), M(rⱼ))`, and either
(a) `hₖ ≠ hₗ` and `hₖ` (respectively `hₗ`) is under-subscribed or prefers `rᵢ` (respectively
`rⱼ`) to at least one of its assigned residents; or (b) `hₖ = hₗ` has at least two free posts;
or (c) `hₖ = hₗ` has one free post and prefers at least one of `rᵢ`, `rⱼ` to some member of
`M(hₖ)`; or (d) `hₖ = hₗ` is full, prefers `rᵢ` to some `rₛ ∈ M(hₖ)`, and prefers `rⱼ` to some
`rₜ ∈ M(hₖ) \ {rₛ}`. -/
def BlockedByCoupleAndPair (i : HospitalsResidentsWithCouplesInstance) (M : ℕ → Option ℕ) :
    Prop :=
  ∃ c ∈ i.2.2, ∃ p ∈ c.2, M c.1.1 ≠ some p.1 ∧ M c.1.2 ≠ some p.2 ∧ CouplePrefers M c p ∧
    ((p.1 ≠ p.2 ∧
        (Undersubscribed i M p.1 ∨ PrefersToSome i p.1 c.1.1 (assigned i M p.1)) ∧
        (Undersubscribed i M p.2 ∨ PrefersToSome i p.2 c.1.2 (assigned i M p.2))) ∨
      (p.1 = p.2 ∧ (assigned i M p.1).length + 2 ≤ capacity i p.1) ∨
      (p.1 = p.2 ∧ (assigned i M p.1).length + 1 = capacity i p.1 ∧
        (PrefersToSome i p.1 c.1.1 (assigned i M p.1) ∨
          PrefersToSome i p.1 c.1.2 (assigned i M p.1))) ∨
      (p.1 = p.2 ∧ (assigned i M p.1).length = capacity i p.1 ∧
        ∃ rs ∈ assigned i M p.1, Prefers (hospitalPrefs i p.1) c.1.1 rs ∧
          PrefersToSome i p.1 c.1.2 ((assigned i M p.1).filter (· ≠ rs))))

/-- `M` is MM-stable (Definition 1): none of the three kinds of blocking holds. -/
def IsMMStable (i : HospitalsResidentsWithCouplesInstance) (M : ℕ → Option ℕ) : Prop :=
  ¬ BlockedBySingle i M ∧ ¬ BlockedByCoupleAndHospital i M ∧ ¬ BlockedByCoupleAndPair i M

/-- There is an MM-stable matching. -/
def HospitalsResidentsWithCouplesFeasible (i : HospitalsResidentsWithCouplesInstance) : Prop :=
  ∃ M : ℕ → Option ℕ, IsMatching i M ∧ IsMMStable i M

open Classical in
/-- HOSPITALS/RESIDENTS WITH COUPLES as a decision problem over bitstrings. -/
noncomputable def hospitalsResidentsWithCouplesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HospitalsResidentsWithCouplesInstance) x with
  | some i => decide (WellFormed i ∧ HospitalsResidentsWithCouplesFeasible i)
  | none => false

/-- **HOSPITALS/RESIDENTS WITH COUPLES is NP-complete.** Source: Ronn (1990); McDermid and
Manlove (2010); Biró, Manlove and McBride (2014), Definition 1 and Theorem 1. -/
public theorem_wanted hospitalsResidentsWithCouples_npComplete :
    hospitalsResidentsWithCouplesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L hospitalsResidentsWithCouplesDec

end MetaMathlibExt.Complexity.NPComplete.HospitalsResidentsWithCouples
