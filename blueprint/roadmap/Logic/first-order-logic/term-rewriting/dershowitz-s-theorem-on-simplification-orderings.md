# Simplification orderings over a finite signature are well-founded

Let $\Sigma$ be a finite signature. Every [simplification ordering](simplification-ordering.md) $\succ$ on $T_\Sigma(X)$ is well-founded, and is therefore a [reduction ordering](reduction-ordering.md).

**Proof.** Suppose $t_1 \succ t_2 \succ \cdots$. If some $x \in \mathrm{var}(t_{i+1}) \setminus \mathrm{var}(t_i)$, then for $\sigma = \{x \mapsto t_i\}$ the subterm property gives $t_{i+1}\sigma \succeq t_i$, while stability gives $t_i = t_i\sigma \succ t_{i+1}\sigma$, contradicting irreflexivity. So all $t_i$ lie in $T_\Sigma(V)$ for the finite set $V = \mathrm{var}(t_1)$. By Kruskal's theorem $t_j \unrhd_{\mathrm{emb}} t_i$ for some $i < j$, hence $t_j \succeq t_i$, contradicting $t_i \succ t_j$.

The hypothesis that $\Sigma$ is finite matters: for infinite signatures the definitions of simplification ordering and embedding must be modified.

## Depends on

- [Simplification ordering](simplification-ordering.md)
- [Reduction ordering](reduction-ordering.md)

## Proof depends on

- [Kruskal's tree theorem](kruskal-s-tree-theorem.md)
- [Simplification orderings contain the embedding](simplification-orderings-contain-the-embedding.md)

## Sources

- U. Waldmann, *Automated Reasoning*, lecture notes, Max Planck Institute for Informatics, winter semester 2019/20, <https://rg1-teaching.mpi-inf.mpg.de/autrea-ws19/script.pdf>, Section 4.5, Theorem 4.27 (Dershowitz) with its proof and the remark on finite signatures, pp. 118–119.
