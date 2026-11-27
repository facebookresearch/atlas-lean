# Graham's LPT rule produces a pure Nash equilibrium

On uniformly related machines, scheduling jobs in nonincreasing order of weight, each on the machine minimizing its resulting load, produces a pure Nash equilibrium. On $m$ identical machines this is Graham's LPT schedule, which is therefore a pure Nash equilibrium with makespan at most $\bigl(\tfrac43 - \tfrac1{3m}\bigr)\mathrm{OPT}$.

## Proof sketch

Jobs inserted later are lighter, so they never make an earlier job want to move: after each insertion, each job's machine plus its own weight remains minimal among the alternatives.

## Depends on

- [Load balancing on uniformly related and unrelated machines](load-balancing-on-uniformly-related-and-unrelated-machines.md)
- [Longest processing time first (LPT)](../../../../ComputerScience/approximation-algorithms/list-scheduling-on-identical-machines/lpt.md)

## Proof depends on

- [Pure Nash equilibria of related load balancing](pure-nash-equilibria-of-related-load-balancing.md)
- [Graham's bound for LPT scheduling](../../../../ComputerScience/approximation-algorithms/list-scheduling-on-identical-machines/lpt-approx.md)

## Sources

- Dimitris Fotakis et al., "The Structure and Complexity of Nash Equilibria for a Selfish Routing Game", Automata, Languages and Programming (ICALP 2002), 2002.
- R. L. Graham, "Bounds on Multiprocessing Timing Anomalies", SIAM Journal on Applied Mathematics, 1969.
- Berthold Vocking, "Selfish Load Balancing", Algorithmic Game Theory, Cambridge University Press, 2007.
