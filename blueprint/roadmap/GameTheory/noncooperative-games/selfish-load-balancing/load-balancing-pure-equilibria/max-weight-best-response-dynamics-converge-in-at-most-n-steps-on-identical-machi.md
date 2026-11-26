# Max-weight best-response dynamics converge in at most n steps on identical machines

On identical machines, consider best-response dynamics in which at each step the unsatisfied job of maximum weight moves to a machine of minimum load. Every job moves at most once, so from any initial assignment the dynamics reach a pure Nash equilibrium after at most $n$ steps, where $n$ is the number of jobs.

## Proof sketch

Once a job moves to a minimum-load machine, later moves of lighter jobs onto its machine cannot make it unsatisfied, because a lighter job moved there only if the machine was minimal and the moved job weighs less.

## Depends on

- [Load balancing on uniformly related and unrelated machines](load-balancing-on-uniformly-related-and-unrelated-machines.md)

## Proof depends on

- [Finite improvement property and price of stability 1 for load balancing](finite-improvement-property-and-price-of-stability-1-for-load-balancing.md)

## Sources

- Eyal Even-Dar, Alexander Kesselman and Yishay Mansour, "Convergence Time to Nash Equilibria", Automata, Languages and Programming (ICALP 2003), 2003.
- Berthold Vocking, "Selfish Load Balancing", Algorithmic Game Theory, Cambridge University Press, 2007.
