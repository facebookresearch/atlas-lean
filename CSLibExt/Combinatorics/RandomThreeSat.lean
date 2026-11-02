/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import CSLibExt.Logics.Propositional.CNF.Semantics
public import CSLibExt.Computability.CookLevin

@[expose] public section

namespace CSLibExt.Combinatorics.RandomThreeSat

/-!
# The random 3-SAT threshold model

The finite uniform model behind the random 3-SAT satisfiability threshold:
on `n` Boolean variables, a clause is a set of three distinct variables with
an independently chosen polarity for each, and a formula of length `m` is an
ordered `m`-tuple of clauses (sampling with replacement). The satisfiability
probability at clause density `r` is the finite counting ratio
`satProb n ⌊r * n⌋₊`; the threshold cutoffs below say that this ratio tends
to `0` above a density and to `1` below it.

Source: Optimization Problems, record 52a, "The complexity threshold of
random 3-SAT", frozen at teorth/optimizationproblems commit
`2c1968cd520b60f1cf3cf50749f7285e800e4e15`; `constants/52a.md` SHA-256
`214acb8d337921d827fcfb8c9f857a2e1a5079cc38384e674e297814079bf876`.

Representation choices, recorded as scope notes rather than theorems:
real densities are realized by `⌊r * n⌋₊` clauses, and the source's
Friedgut sequence `r_{3,n}` is represented by its cutoff consequences
(`IsLowerCutoff` / `IsUpperCutoff`); no Friedgut sequence is constructed
here. The totalized `sInf`/`sSup` thresholds return a real number for every
cutoff set (junk values when the one-sided hypotheses fail); they carry
the usual infimum/supremum meaning under one-sided hypotheses only:
`sInf` of the upper-cutoff set requires it to be nonempty and bounded
below, and `sSup` of the lower-cutoff set requires it to be nonempty and
bounded above. (Nonempty upper-cutoff sets are automatically unbounded
above, and nonempty lower-cutoff sets unbounded below, by monotonicity.)
The literature bounds in `WantedExt` supply the needed bounds as proof
requests.
-/

/-- **3-clause.** A 3-clause on $n$ variables is a pair $(S, p)$ of a three-element set $S$ of
variables among the $n$ and a polarity $p$ assigning a Boolean value to every variable, with
$p$ equal to false at every variable outside $S$. This normalization gives each clause in the
usual sense (a three-element variable set with one of $2^3$ polarity patterns) exactly one
representative. -/
def Clause (n : ℕ) :=
  { p : Finset (Fin n) × (Fin n → Bool) //
    p.1.card = 3 ∧ ∀ i : Fin n, i ∉ p.1 → p.2 i = false }

noncomputable instance (n : ℕ) :
    DecidablePred (fun p : Finset (Fin n) × (Fin n → Bool) =>
      p.1.card = 3 ∧ ∀ i : Fin n, i ∉ p.1 → p.2 i = false) :=
  fun _ => Classical.propDecidable _

noncomputable instance (n : ℕ) : Fintype (Clause n) :=
  Subtype.fintype _

/-- **Formulas of the random 3-SAT model.** A formula with $m$ clauses on $n$ variables is an
ordered $m$-tuple of 3-clauses on $n$ variables, that is, a function from $\{0, \dots, m - 1\}$
to the set of 3-clauses on $n$ variables.

With the uniform counting measure, this finite set of formulas is the sample space of $m$
clauses chosen uniformly and independently, with replacement. -/
abbrev Formula (n m : ℕ) := Fin m → Clause n

/-- **Satisfaction of a 3-clause.** An assignment $a$ of Boolean values to $n$ variables
satisfies a 3-clause $c$ on these variables when $a$ gives at least one of the three variables
of $c$ the polarity that $c$ prescribes for it. -/
def clauseSat {n : ℕ} (a : Fin n → Bool) (c : Clause n) : Prop :=
  ∃ i ∈ c.1.1, a i = c.1.2 i

/-- **Satisfiable 3-SAT formulas.** A formula $F$ with $m$ clauses on $n$ variables is
satisfiable when there is an assignment $a$ of Boolean values to the $n$ variables that
satisfies every clause of $F$, that is, $a$ satisfies the 3-clause $F(j)$ for every
$j \in \{0, \dots, m - 1\}$. -/
def Satisfiable {n m : ℕ} (F : Formula n m) : Prop :=
  ∃ a : Fin n → Bool, ∀ j : Fin m, clauseSat a (F j)

noncomputable instance {n m : ℕ} : DecidablePred (Satisfiable (n := n) (m := m)) :=
  fun _ => Classical.propDecidable _

noncomputable instance {n m : ℕ} : Fintype { F : Formula n m // Satisfiable F } :=
  Subtype.fintype _

/-- **Satisfiability probability of random 3-SAT.** For natural numbers $n$ and $m$, the
satisfiability probability $p(n, m)$ is the number of satisfiable formulas with $m$ clauses on
$n$ variables divided by the number of all such formulas, that is, the probability that a
uniformly random formula with $m$ clauses on $n$ variables is satisfiable. When there are no such
formulas, which happens exactly when $n < 3$ and $m > 0$, the quotient is taken to be $0$; this
affects only finitely many $n$ in any asymptotic statement. -/
noncomputable def satProb (n m : ℕ) : ℝ :=
  (Fintype.card { F : Formula n m // Satisfiable F } : ℝ) /
    (Fintype.card (Formula n m) : ℝ)

theorem satProb_nonneg (n m : ℕ) : 0 ≤ satProb n m :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem satProb_le_one {n m : ℕ} :
    satProb n m ≤ 1 := by
  by_cases h : Fintype.card (Formula n m) = 0
  · have hempty : Fintype.card { F : Formula n m // Satisfiable F } = 0 :=
      Nat.eq_zero_of_le_zero (h ▸ Fintype.card_subtype_le _)
    simp [satProb, h, hempty]
  · have hpos : 0 < Fintype.card (Formula n m) := Nat.pos_of_ne_zero h
    have hle : Fintype.card { F : Formula n m // Satisfiable F } ≤
        Fintype.card (Formula n m) :=
      Fintype.card_subtype_le _
    rw [satProb, div_le_one (by exact_mod_cast hpos)]
    exact_mod_cast hle

/-- **3-clauses exist on at least three variables.** If $n \ge 3$, then there is a 3-clause on
$n$ variables: take the first three variables, with polarity true on them and the normalized
polarity false elsewhere. -/
theorem clause_nonempty {n : ℕ} (hn : 3 ≤ n) : Nonempty (Clause n) := by
  classical
  refine ⟨⟨Finset.univ.image (Fin.castLE hn),
    fun i => decide (i ∈ Finset.univ.image (Fin.castLE hn))⟩, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ (Fin.castLE_injective hn), Finset.card_univ,
      Fintype.card_fin]
  · intro i hi
    simp [hi]

theorem formula_card_pos {n m : ℕ} (hn : 3 ≤ n) :
    0 < Fintype.card (Formula n m) := by
  obtain ⟨c⟩ := clause_nonempty hn
  exact Fintype.card_pos_iff.mpr ⟨fun _ => c⟩

/-- **Satisfiability probability with no clauses.** For every number $n$ of variables, the
probability that a uniformly random formula with $0$ clauses on $n$ variables is satisfiable is
$1$: the only such formula is the empty one, and every assignment satisfies it. -/
theorem satProb_zero (n : ℕ) : satProb n 0 = 1 := by
  have h1 : Fintype.card (Formula n 0) = 1 :=
    Fintype.card_ofSubsingleton (fun i => i.elim0)
  have h2 : Fintype.card { F : Formula n 0 // Satisfiable F } = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨fun i => i.elim0, fun _ => true, fun j => j.elim0⟩, ?_⟩
    rintro ⟨F, -⟩
    apply Subtype.ext
    funext i
    exact i.elim0
  rw [satProb, h1, h2]
  norm_num

/-- **Upper threshold cutoff.** A real number $\rho$ is an upper threshold cutoff for random
3-SAT when, for every real $r > \rho$, the probability that a uniformly random formula with
$\lfloor r n \rfloor$ clauses on $n$ variables is satisfiable tends to $0$ as $n \to \infty$
(when $r n < 0$ the formula has no clauses); equivalently, such a formula is unsatisfiable
with probability tending to $1$.

Literature upper bounds on the threshold are exactly cutoffs in this sense. -/
def IsUpperCutoff (ρ : ℝ) : Prop :=
  ∀ r : ℝ, ρ < r →
    Filter.Tendsto (fun n : ℕ => satProb n ⌊r * (n : ℝ)⌋₊) Filter.atTop (nhds 0)

/-- **Lower threshold cutoff.** A real number $\rho$ is a lower threshold cutoff for random
3-SAT when, for every real $r < \rho$, the probability that a uniformly random formula with
$\lfloor r n \rfloor$ clauses on $n$ variables is satisfiable tends to $1$ as $n \to \infty$
(when $r n < 0$ the formula has no clauses). -/
def IsLowerCutoff (ρ : ℝ) : Prop :=
  ∀ r : ℝ, r < ρ →
    Filter.Tendsto (fun n : ℕ => satProb n ⌊r * (n : ℝ)⌋₊) Filter.atTop (nhds 1)

theorem IsUpperCutoff.mono {ρ ρ' : ℝ} (hρ : IsUpperCutoff ρ) (h : ρ ≤ ρ') :
    IsUpperCutoff ρ' :=
  fun r hr => hρ r (h.trans_lt hr)

theorem IsLowerCutoff.anti {ρ ρ' : ℝ} (hρ : IsLowerCutoff ρ) (h : ρ' ≤ ρ) :
    IsLowerCutoff ρ' :=
  fun r hr => hρ r (hr.trans_le h)

/-- **Upper threshold of random 3-SAT.** The upper threshold is the infimum, in the real numbers,
of the set of upper threshold cutoffs: the reals $\rho$ such that, for every real $r > \rho$, the
probability that a uniformly random formula with $\lfloor rn \rfloor$ clauses on $n$ variables
(no clauses when $rn < 0$) is satisfiable tends to $0$ as $n \to \infty$. The infimum is taken
to be $0$ when this set is empty or unbounded below.

Under the cutoff characterization of the source's Friedgut sequence $r_{3,n}$, this is the limsup
of that sequence. -/
noncomputable def upperThreshold : ℝ :=
  sInf { ρ : ℝ | IsUpperCutoff ρ }

/-- **Lower threshold of random 3-SAT.** The lower threshold is the supremum, in the real numbers,
of the set of lower threshold cutoffs: the reals $\rho$ such that, for every real $r < \rho$, the
probability that a uniformly random formula with $\lfloor rn \rfloor$ clauses on $n$ variables
(no clauses when $rn < 0$) is satisfiable tends to $1$ as $n \to \infty$. The supremum is taken
to be $0$ when this set is empty or unbounded above.

It is the liminf counterpart of the upper threshold. -/
noncomputable def lowerThreshold : ℝ :=
  sSup { ρ : ℝ | IsLowerCutoff ρ }

/-- **Random 3-SAT threshold conjecture.** There is a real number $c$ that is both a lower and
an upper threshold cutoff: for every real $r < c$, the probability that a uniformly random
formula with $\lfloor r n \rfloor$ clauses on $n$ variables is satisfiable tends to $1$ as
$n \to \infty$, and for every real $r > c$ this probability tends to $0$ (when $r n < 0$ the
formula has no clauses).

This is stated as a proposition, not asserted: the existence of such a constant is open,
whereas Friedgut's sharp-threshold theorem is proved. -/
def HasConstantThreshold : Prop :=
  ∃ c : ℝ, IsLowerCutoff c ∧ IsUpperCutoff c

/-- **Clauses as variable sets with polarity patterns.** For every $n$, the 3-clauses on $n$
variables correspond bijectively to the pairs $(S, q)$ of a three-element set $S$ of variables
among the $n$ and a Boolean polarity $q$ on the variables of $S$: a clause is sent to its
variable set together with its polarity restricted to that set. -/
def clauseEquiv (n : ℕ) :
    Clause n ≃ Σ s : { s : Finset (Fin n) // s.card = 3 }, (s.1 : Type _) → Bool where
  toFun c := ⟨⟨c.1.1, c.2.1⟩, fun i => c.1.2 i.1⟩
  invFun sq :=
    ⟨(sq.1.1, fun i => if h : i ∈ sq.1.1 then sq.2 ⟨i, h⟩ else false), sq.1.2,
      fun i hi => by simp [hi]⟩
  left_inv c := by
    apply Subtype.ext
    show (c.1.1, fun i => if h : i ∈ c.1.1 then c.1.2 i else false) = c.1
    refine Prod.ext rfl ?_
    funext i
    by_cases h : i ∈ c.1.1
    · simp [h]
    · simp [h, c.2.2 i h]
  right_inv sq := by
    obtain ⟨⟨s, hs⟩, q⟩ := sq
    show (⟨⟨s, hs⟩, fun i : s => if h : i.1 ∈ s then q ⟨i.1, h⟩ else false⟩ :
        Σ s : { s : Finset (Fin n) // s.card = 3 }, (s.1 : Type _) → Bool) =
      ⟨⟨s, hs⟩, q⟩
    have hfun : (fun i : s => if h : i.1 ∈ s then q ⟨i.1, h⟩ else false) = q := by
      funext ⟨i, hi⟩
      simp [hi]
    rw [hfun]

theorem card_clause (n : ℕ) :
    Fintype.card (Clause n) = 8 * n.choose 3 := by
  rw [Fintype.card_congr (clauseEquiv n), Fintype.card_sigma]
  have hsub : Fintype.card { s : Finset (Fin n) // s.card = 3 } = n.choose 3 := by
    rw [Fintype.card_subtype]
    have hfilter : Finset.univ.filter (fun s : Finset (Fin n) => s.card = 3) =
        Finset.powersetCard 3 Finset.univ := by
      ext s
      simp [Finset.mem_powersetCard]
    rw [hfilter, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  have hfun : ∀ s : { s : Finset (Fin n) // s.card = 3 },
      Fintype.card ((s.1 : Type _) → Bool) = 8 := by
    intro s
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe, s.2]
    norm_num
  rw [← hsub, Finset.sum_congr rfl (fun s _ => hfun s), Finset.sum_const,
    Finset.card_univ]
  simp [mul_comm]

/-! ### Bridge to the canonical CNF semantics

The model's own `clauseSat`/`Satisfiable` are the finite counting model's
native predicates. For interoperability with the library's SAT
infrastructure, a clause converts to a canonical `Cslib.Logic.PL`
clause (literals as `(variable index, polarity)` pairs) and a formula to
a canonical CNF formula; satisfiability agrees with `Cslib.Logic.PL.CNFSat`
under the obvious extension of a finite assignment to all of `ℕ`. -/

/-- **CNF clause of a random 3-SAT clause.** The CNF clause of a clause $c$ on $n$ variables is the
list of literals $(i, b_i)$, one for each of the three variables $i$ of $c$ taken as a
natural-number index, where $b_i$ is the polarity that $c$ prescribes for $i$; the literals are
listed in some fixed order. -/
noncomputable def toCNFClause {n : ℕ} (c : Clause n) : Cslib.Logic.PL.CNFClause :=
  c.1.1.toList.map (fun i => (i.val, c.1.2 i))

/-- **Extension of an assignment by false.** An assignment $a$ of Boolean values to the variables
$0, \dots, n - 1$ extends to all natural-number variables by giving variable $i$ the value $a(i)$
when $i < n$ and the value false otherwise. -/
def extendAssign {n : ℕ} (a : Fin n → Bool) : ℕ → Bool :=
  fun i => if h : i < n then a ⟨i, h⟩ else false

theorem clauseSat_iff {n : ℕ} (a : Fin n → Bool) (c : Clause n) :
    clauseSat a c ↔
      Cslib.Logic.PL.CNFClause.Satisfies (extendAssign a) (toCNFClause c) := by
  constructor
  · rintro ⟨i, hi, hsat⟩
    refine ⟨(i.val, c.1.2 i),
      List.mem_map.mpr ⟨i, Finset.mem_toList.mpr hi, rfl⟩, ?_⟩
    have hlt : i.val < n := i.2
    have hfin : (⟨i.val, hlt⟩ : Fin n) = i := Fin.ext rfl
    show extendAssign a i.val = c.1.2 i
    simp [extendAssign, hlt, hfin, hsat]
  · rintro ⟨⟨v, p⟩, hmem, hsat⟩
    simp only [toCNFClause, Finset.mem_toList, List.mem_map] at hmem
    obtain ⟨i, hi, hlit⟩ := hmem
    injection hlit with hv hp
    refine ⟨i, hi, ?_⟩
    have hlt : i.val < n := i.2
    have hfin : (⟨i.val, hlt⟩ : Fin n) = i := Fin.ext rfl
    have hsat' : extendAssign a v = p := hsat
    rw [← hv] at hsat'
    simp [extendAssign, hlt, hfin] at hsat'
    rw [hp]
    exact hsat'

/-- **Satisfying a clause through a restricted assignment.** Let $A$ assign a Boolean value to
every natural-number variable, and let $c$ be a 3-clause on the $n$ variables $0, \dots, n - 1$.
Then the restriction of $A$ to these $n$ variables satisfies $c$ if and only if $A$ satisfies
the CNF clause of $c$: the list with one literal $(i, p_i)$ for each of the three variables $i$
of $c$, where $p_i$ is the polarity that $c$ prescribes at $i$. A CNF clause is satisfied when
$A$ gives the variable of at least one of its literals that literal's polarity. -/
theorem clauseSat_restrict_iff {n : ℕ} (A : ℕ → Bool) (c : Clause n) :
    clauseSat (fun i => A i.val) c ↔
      Cslib.Logic.PL.CNFClause.Satisfies A (toCNFClause c) := by
  constructor
  · rintro ⟨i, hi, hsat⟩
    exact ⟨(i.val, c.1.2 i),
      List.mem_map.mpr ⟨i, Finset.mem_toList.mpr hi, rfl⟩, hsat⟩
  · rintro ⟨⟨v, p⟩, hmem, hsat⟩
    simp only [toCNFClause, Finset.mem_toList, List.mem_map] at hmem
    obtain ⟨i, hi, hlit⟩ := hmem
    injection hlit with hv hp
    refine ⟨i, hi, ?_⟩
    have hsat' : A v = p := hsat
    rw [← hv] at hsat'
    rw [hp]
    exact hsat'

/-- **CNF formula of a random 3-SAT formula.** The CNF formula of a formula $F$ with $m$ clauses
$F_0, \dots, F_{m-1}$ on $n$ variables is the list of the CNF clauses of $F_0, \dots, F_{m-1}$,
in this order. -/
noncomputable def toCNF {n m : ℕ} (F : Formula n m) : Cslib.Logic.PL.CNF :=
  (List.ofFn F).map toCNFClause

/-- **Random 3-SAT satisfiability agrees with CNF satisfiability.** A formula $F$ with $m$ clauses
on $n$ variables is satisfiable if and only if its CNF formula, which lists each clause of $F$ as
its three literals (variable index, polarity), is satisfiable as a CNF formula: some assignment
of truth values to all natural-number variable indices makes at least one literal of every
clause true. -/
theorem satisfiable_iff {n m : ℕ} (F : Formula n m) :
    Satisfiable F ↔ Cslib.Logic.PL.CNFSat (toCNF F) := by
  rw [Cslib.Logic.PL.cnfSat_iff_exists_satisfies]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨extendAssign a, ?_⟩
    intro cl hcl
    simp only [toCNF, List.mem_map, List.mem_ofFn] at hcl
    obtain ⟨c, ⟨j, rfl⟩, rfl⟩ := hcl
    exact (clauseSat_iff a (F j)).mp (ha j)
  · rintro ⟨A, hA⟩
    refine ⟨fun i => A i.val, fun j => ?_⟩
    have hcl : toCNFClause (F j) ∈ toCNF F := by
      simp [toCNF, List.mem_ofFn]
    exact (clauseSat_restrict_iff A (F j)).mpr (hA _ hcl)

end CSLibExt.Combinatorics.RandomThreeSat
