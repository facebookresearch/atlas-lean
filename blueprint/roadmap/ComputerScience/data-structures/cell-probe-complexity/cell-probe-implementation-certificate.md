# Cell-probe implementation certificate

A *cell-probe implementation* of a specification $D$ from an abstract initial state $s_0$ is a cell-probe scheme in $S$ cells of $w$ bits together with a representation relation between abstract states and memories, an integer potential $\Phi \ge 0$ and an amortized probe charge $c(s, o)$, such that from every represented memory each admissible operation's probe tree returns a specified answer, ends in a memory representing a specified next state, and makes at most $c(s, o) + \Phi(m) - \Phi(m')$ probes. A randomized version couples the memory with a latent seed drawn from a reference law and bounds expected probes against oblivious operation sequences. Word-RAM implementation certificates translate into cell-probe ones by simulation.

## Depends on

- [Deterministic dynamic cell-probe scheme](deterministic-cell-probe-scheme.md)
- [Randomized cell-probe scheme with private coins](randomized-cell-probe-scheme.md)
- [State-transition specification of a data structure](../data-structure-interfaces-and-refinement/state-transition-specification.md)
- [Word-RAM implementation certificate with potential-amortized running time](../data-structure-interfaces-and-refinement/word-ram-implementation-certificate.md)
- [Simulation of Word-RAM data structures by cell-probe schemes](word-ram-simulation-by-cell-probe-schemes.md)

## Sources

- P. B. Miltersen, "Cell Probe Complexity - a Survey", Advances in Data Structures Workshop (FSTTCS pre-conference workshop), 1999.
- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd edition, MIT Press, 2009.
