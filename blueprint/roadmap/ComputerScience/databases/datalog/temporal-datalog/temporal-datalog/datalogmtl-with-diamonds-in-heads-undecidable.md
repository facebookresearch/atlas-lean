# Consistency of propositional datalogMTL with diamonds in rule heads is undecidable

DatalogMTL extends datalog with metric temporal operators over dense time. Allowing the existential operators "sometime within a range in the future or past" in rule heads makes consistency checking undecidable, already for propositional programs, whereas the Horn language without them is EXPSPACE-complete.

**Setting (Brandt, Güzel Kalaycı, Ryzhikov, Xiao and Zakharyaschev).** Ranges $\varrho$ are intervals with non-negative endpoints in the dyadic rationals or $\infty$, written in binary. Atoms are given by

$$
A ::= P(\tau_1, \dots, \tau_m) \mid \top \mid \boxplus_\varrho A \mid \boxminus_\varrho A \mid \diamondplus_\varrho A \mid \diamondminus_\varrho A \mid A\, \mathcal{U}_\varrho\, A' \mid A\, \mathcal{S}_\varrho\, A',
$$

interpreted over the real line: $\boxplus_\varrho A$ holds at $t$ if $A$ holds at every $s$ with $s - t \in \varrho$, $\diamondplus_\varrho A$ if at some such $s$, the past operators $\boxminus_\varrho, \diamondminus_\varrho$ symmetrically, and $\mathcal{U}_\varrho, \mathcal{S}_\varrho$ as metric until and since. A datalogMTL program is a finite set of rules $A^+ \leftarrow A_1 \wedge \dots \wedge A_k$ or $\bot \leftarrow A_1 \wedge \dots \wedge A_k$ ($k \ge 1$), where body atoms may also be inequalities of terms and the head atom $A^+$ may use only $\boxplus_\varrho$ and $\boxminus_\varrho$. In *datalogMTL$^\Diamond$* the head may also use $\diamondplus_\varrho$ and $\diamondminus_\varrho$. A data instance is a finite set of facts $P(\vec{c})@\iota$ stating that $P(\vec{c})$ holds throughout the interval $\iota$, where an interval is a nonempty set of the form $[t_1, t_2]$, $[t_1, t_2)$, $(t_1, t_2]$ or $(t_1, t_2)$ with $t_1 \le t_2$ in the dyadic rationals or $\pm\infty$, endpoints written in binary. A program $\Pi$ and a data instance $\mathcal{D}$ are *consistent* if some interpretation satisfies every rule at every time point under every assignment and makes every fact of $\mathcal{D}$ true throughout its interval. A program is *propositional* if all its predicates are nullary.

**Theorem (Brandt, Güzel Kalaycı, Ryzhikov, Xiao and Zakharyaschev).** Consistency checking for propositional datalogMTL$^\Diamond$ programs is undecidable: no algorithm decides, given a propositional datalogMTL$^\Diamond$ program $\Pi$ and a data instance $\mathcal{D}$, whether $\Pi$ and $\mathcal{D}$ are consistent. The proof reduces from the non-halting problem for two-counter Minsky machines started with both counters $0$ (Theorem 10 of the source).

For datalogMTL itself (no diamonds in heads) consistency checking is EXPSPACE-complete in combined complexity, and EXPSPACE-hard already for propositional programs; full propositional MTL with punctual ranges is undecidable (Alur and Henzinger).

## Depends on

- [Datalog programs and the immediate consequence operator](../../datalog-programs-and-the-immediate-consequence-operator.md)
- [Decidability by multi-stack machines](../../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The reduction is from the non-halting problem of two-counter Minsky machines started with both counters at zero, adapting a construction for a non-Horn fragment of MTL. Successive configurations occupy the time intervals $[0,4), [4,8), \dots$: a propositional variable $P_i$ at the first point $4m$ of the $m$-th interval records the current instruction, and the values of the counters are encoded by the number of time points carrying marker variables inside the interval. The data instance $P_1@[0,0]$, $Z@(1,2)$, $Z@(3,4)$ encodes the initial configuration. Rules with punctual ranges copy markers from one interval to the next, while diamonds in heads let increments create a new marker somewhere in a gap; a rule $\bot \leftarrow P_n$ makes the program inconsistent exactly when the halting instruction is reached.

## Sources

- Sebastian Brandt, Elem Güzel Kalaycı, Vladislav Ryzhikov, Guohui Xiao and Michael Zakharyaschev, "Querying Log Data with Metric Temporal Logic", Journal of Artificial Intelligence Research 62, pp. 829–877, 2018, <https://doi.org/10.1613/jair.1.11229>; read in arXiv:1703.08982v3, <https://arxiv.org/abs/1703.08982v3>: Section 2 (datalogMTL, data instances, consistency), Theorem 8 (EXPSPACE-completeness) and Theorem 10 (main statement), in the numbering of that version.
