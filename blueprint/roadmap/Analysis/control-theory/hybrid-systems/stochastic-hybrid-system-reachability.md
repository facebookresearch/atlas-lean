# Qualitative reachability for stochastic hybrid systems with simple features is undecidable

For hybrid systems whose delays, edge choices and resets are drawn at random, deciding whether a target set is reached with probability one, or with probability zero, is undecidable already with continuous delay distributions, linear guards and positive integer slopes; so is approximating the reachability probability within any precision below one half.

**Stochastic hybrid systems.** A hybrid system has finitely many locations, real variables $x_1, \ldots, x_n$, a continuous flow function for each location, location invariants, and edges with guards and reset relations. A stochastic hybrid system adds, for each state, a probability distribution on the delay before leaving the location (supported on the delays after which some edge is enabled), a distribution on the enabled edges giving positive weight to each, and for each edge a distribution on the possible resets. From an initial distribution $\mu$ this defines a probability measure on runs; $\Pr_\mu(\mathsf F B)$ is the probability that a run visits a measurable target set $B$.

**Theorem (Bouyer, Brihaye, Randour, Rivière and Vandenhove).** The qualitative reachability problems, deciding whether $\Pr_\mu(\mathsf F B) = 1$ and whether $\Pr_\mu(\mathsf F B) = 0$, are undecidable for stochastic hybrid systems with purely continuous distributions on time delays, guards that are linear comparisons of variables and constants, and positive integer slopes for the flow of the variables. The approximate quantitative reachability problem, deciding for rational $p$ and $\epsilon > 0$ whether $|\Pr_\mu(\mathsf F B) - p| < \epsilon$, is undecidable for these systems as well, for every fixed precision $\epsilon < 1/2$.

It follows that deciding whether a state lies in the avoid-set of $B$, the states from which $B$ is reached with probability $0$, is undecidable too. The same paper shows that both qualitative problems become decidable for cycle-reset stochastic hybrid systems (those with a strong reset on every cycle) that are definable in an o-minimal structure with a decidable theory, under a further technical assumption (Proposition 3.15), for instance for such systems definable over the real algebraic numbers.

## Depends on

- [Hybrid automata and their executions](hybrid-automata-and-their-executions.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The proof reduces the halting problem for two-counter machines to deciding whether a measurable set is reached with probability $1$, taking inspiration from a construction of Henzinger and Raskin for nondeterministic hybrid systems; the copy read describes this reduction but does not contain its proof. Because the systems built reach the target with probability either $0$ or $1$, an approximation within $\epsilon < 1/2$ would solve the qualitative problem.

## Sources

- Patricia Bouyer, Thomas Brihaye, Mickael Randour, Cédric Rivière and Pierre Vandenhove, "Decisiveness of stochastic systems and its application to hybrid models", in *Proceedings of the 11th International Symposium on Games, Automata, Logics, and Formal Verification (GandALF 2020)*, Electronic Proceedings in Theoretical Computer Science 326, 2020, pp. 149–165, <https://doi.org/10.4204/EPTCS.326.10>; read as arXiv:2001.04347v2, <https://arxiv.org/abs/2001.04347v2>: Definition 2.2 of the qualitative and quantitative reachability problems in Section 2, Definitions 3.1 and 3.3 and Proposition 3.6 ("Undecidability of SHSs") with the discussion around it, Definition 3.7 and Proposition 3.15 in Section 3, of that version.
