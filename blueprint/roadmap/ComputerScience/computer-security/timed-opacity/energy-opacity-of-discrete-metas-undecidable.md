# Energy opacity of discrete multi-energy timed automata is undecidable

An attacker who observes only the final energy levels (and possibly the execution time) of a run should not learn whether it visited a secret location. For guarded multi-energy timed automata whose energies change only along edges, every variant of this opacity question is undecidable with two energy variables and one clock.

**Setting (André and Bakiri).** A *guarded multi-energy timed automaton* (guarded META) has finitely many locations with an initial location, a nonempty set of *private* locations and a set of *final* locations; finitely many real-valued clocks and nonnegative real energy variables; location invariants and edge guards that are *simple constraints*, conjunctions of comparisons $v \bowtie d$ of a clock or energy $v$ with an integer $d$; integer energy rates in each location; and edges that reset clocks and update energies. It is *discrete* if energies change only by updates along edges. A run reaching a final location is *private* if it visits a private location and *public* if it visits none. With $\mathrm{Priv}_{\mathrm{EN}}$ and $\mathrm{Pub}_{\mathrm{EN}}$ the sets of final energy vectors of private and public runs, the automaton is *fully EN-opaque* if $\mathrm{Priv}_{\mathrm{EN}} = \mathrm{Pub}_{\mathrm{EN}}$, *weakly EN-opaque* if $\mathrm{Priv}_{\mathrm{EN}} \subseteq \mathrm{Pub}_{\mathrm{EN}}$, and *$\exists$-EN-opaque* if $\mathrm{Priv}_{\mathrm{EN}} \cap \mathrm{Pub}_{\mathrm{EN}} \neq \emptyset$. The *ET-EN* variants use the pairs of duration and final energy vector instead.

**Theorem (André and Bakiri).** For each $\star \in \{\exists, \text{weak}, \text{full}\}$ and each observation $\mathrm{O} \in \{\mathrm{EN}, \text{ET-EN}\}$, it is undecidable whether a discrete guarded META with $2$ energy variables and $1$ clock is $\star$-$\mathrm{O}$-opaque.

The same paper proves the corresponding undecidability when the attacker observes the energy at every time unit, and decidability for several subclasses, notably with a single energy variable or with only positive rates.

## Depends on

- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)
- [Halting is undecidable](../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

The proof first shows that reachability of a location is undecidable for discrete guarded METAs with two energy variables and one clock that stays $0$, so the runs take zero time: the two energies hold the two counters of a deterministic two-counter machine, increments and decrements are energy updates on edges, and zero tests are guards $e = 0$ and $e > 0$. Each opacity variant is then shown to be at least as hard as reachability. For EN-opacity, from the initial location a fresh private location with self-loops incrementing each energy leads to a fresh final location, so every energy vector is a private final energy; from the target location a fresh location with self-loops incrementing and decrementing each energy leads to the same final location. If the target is reachable, public runs also realize every energy vector and all three opacity notions hold; otherwise there are no public runs and none holds. A good expansion links a page for the undecidability of location reachability for discrete guarded METAs with two energy variables and one clock, the first step of the proof.

## Sources

- Étienne André and Lydia Bakiri, "Opacity problems in multi-energy timed automata", Proceedings of the 41st ACM/SIGAPP Symposium on Applied Computing (SAC 2026), pp. 317–324, 2026, <https://doi.org/10.1145/3748522.3779881>; the definitions of Sections 2 and 3 (Definitions 3 and 4, ET- and EN-opacity), Proposition 2 in Section 5 ("Opacity problems for discrete METAs") with Theorems 1 and 2 (decidability for discrete positive METAs), and the proof of Proposition 2 in the appendix (two-counter machines and the reachability lemma, Lemma 1 in Section E.1.2) of arXiv:2512.04950v1, read at <https://arxiv.org/abs/2512.04950v1>.
