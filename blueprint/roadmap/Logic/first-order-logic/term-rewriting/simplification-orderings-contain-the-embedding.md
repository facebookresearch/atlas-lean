# Simplification orderings contain the embedding

Let $\succ$ be a [simplification ordering](simplification-ordering.md) on $T_\Sigma(X)$ and $\succeq$ its reflexive closure. Then $s \rhd_{\mathrm{emb}} t$ implies $s \succ t$, and $s \unrhd_{\mathrm{emb}} t$ implies $s \succeq t$.

**Proof.** By transitivity it suffices to show that $s \to_{R_{\mathrm{emb}}} t$ implies $s \succ t$. Every rule $l \to r$ of $R_{\mathrm{emb}}$ has $l \rhd r$, hence $l \succ r$ by the subterm property, and $\succ$ is a rewrite relation.

## Depends on

- [Simplification ordering](simplification-ordering.md)

## Sources

- U. Waldmann, *Automated Reasoning*, lecture notes, Max Planck Institute for Informatics, winter semester 2019/20, <https://rg1-teaching.mpi-inf.mpg.de/autrea-ws19/script.pdf>, Section 4.5, Lemma 4.25 with its proof, p. 118.
