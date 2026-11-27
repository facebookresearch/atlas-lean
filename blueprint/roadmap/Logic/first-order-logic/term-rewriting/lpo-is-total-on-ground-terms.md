# The lexicographic path ordering is total on ground terms

If the precedence $\succ$ is total on the function symbols of $\Sigma$, then the [lexicographic path ordering](lexicographic-path-ordering.md) $\succ_{\mathrm{lpo}}$ is total on ground terms: for all $s, t \in T_\Sigma(\emptyset)$, $s \succ_{\mathrm{lpo}} t$ or $t \succ_{\mathrm{lpo}} s$ or $s = t$.

**Proof.** Induction on $|s| + |t|$ with a case analysis.

## Depends on

- [Lexicographic path ordering](lexicographic-path-ordering.md)

## Sources

- U. Waldmann, *Automated Reasoning*, lecture notes, Max Planck Institute for Informatics, winter semester 2019/20, <https://rg1-teaching.mpi-inf.mpg.de/autrea-ws19/script.pdf>, Section 4.5, Theorem 4.30, p. 120.
