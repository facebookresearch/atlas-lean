# Polynomial interpretations give reduction orderings

For a [polynomial interpretation](polynomial-interpretation.md), the ordering $s \succ t$ iff $P_s > P_t$ is a [reduction ordering](../reduction-ordering.md). Hence a term rewriting system terminates if $P_l > P_r$ for each of its rules $l \to r$.

**Proof.** The interpretations are monotone maps on the well-founded set $(U, >)$, so [monotone interpretations give reduction orderings](../monotone-interpretations-give-reduction-orderings.md); and $s \succ_{\mathcal A} t$ holds exactly when $P_s > P_t$. A system whose rules all satisfy $l \succ r$ for a reduction ordering terminates, by [the characterization of termination](../reduction-orderings-characterize-termination.md).

## Depends on

- [Polynomial interpretation](polynomial-interpretation.md)
- [Reduction ordering](../reduction-ordering.md)

## Proof depends on

- [Monotone interpretations give reduction orderings](../monotone-interpretations-give-reduction-orderings.md)
- [Reduction orderings characterize termination](../reduction-orderings-characterize-termination.md)

## Sources

- U. Waldmann, *Automated Reasoning*, lecture notes, Max Planck Institute for Informatics, winter semester 2019/20, <https://rg1-teaching.mpi-inf.mpg.de/autrea-ws19/script.pdf>, Section 4.5, polynomial orderings as an instance of the interpretation method (Theorem 4.22) and the remark $s \succ_{\mathcal A} t$ iff $P_s > P_t$, pp. 116–117; Theorem 4.19 for termination via reduction orderings.
