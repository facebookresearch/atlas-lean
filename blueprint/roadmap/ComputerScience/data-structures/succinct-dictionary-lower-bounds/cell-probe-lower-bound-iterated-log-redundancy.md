# Cell-probe lower bound Ω(k) for dynamic dictionaries with n·log^(k) n redundancy

For every $\alpha > 0$, $c_R \ge 0$ and $c_w \ge 0$ there is a constant $c > 0$ such that the following holds for all $U, V, n, k$ with $2 \le n$, $4n \le U$, $n^{1+\alpha} \le U$, $V \ge 1$ and $1 \le k \le \log^* n$. Let a deterministic step-indexed or zero-error randomized cell-probe scheme with $S$ cells of $w \le c_w(\log_2 U + \log_2 V)$ bits implement the dynamic dictionary with at most $n$ keys exactly on all admissible histories of length at most $4n+1$, using

$$
S w \le \log_2 \binom{U}{n} + n \log_2 V + c_R \cdot n \cdot \max(\log^{(k)} n, 1)
$$

bits. Then on the insert–query–delete distribution ($4n$ operations) its expected total number of probes is at least $c \cdot n \cdot k$. In particular, with $O(n)$ bits of redundancy every such scheme makes $\Omega(\log^* n)$ expected probes per operation.

## Proof sketch

Choose a meta-operation tree with roughly $k$ levels whose fanouts grow like iterated exponentials, so that the redundancy budget $c_R n \log^{(k)} n$ satisfies the outer lemma's condition at every level. Each level then contributes $\Omega(n)$ probes and the attributions are disjoint, giving $\Omega(nk)$. Coin fixing transfers the bound from deterministic step-indexed schemes to zero-error randomized ones.

## Depends on

- [Deterministic dynamic cell-probe scheme](../cell-probe-complexity/deterministic-cell-probe-scheme.md)
- [Randomized cell-probe scheme with private coins](../cell-probe-complexity/randomized-cell-probe-scheme.md)
- [Hard operation distributions for dynamic dictionaries](hard-operation-distributions.md)
- [Information-theoretic space bound for dictionaries](../hashing/succinct-dictionaries-and-hash-families/dictionary-specifications/information-theoretic-dictionary-space.md)
- [Iterated logarithm and log-star](../hashing/succinct-dictionaries-and-hash-families/dictionary-specifications/iterated-logarithm.md)

## Proof depends on

- [Outer lemma: each tree level forces linearly many probes](outer-lemma.md)
- [Meta-operation tree and probe attribution](meta-operation-tree.md)
- [Coin fixing for zero-error randomized cell-probe schemes](../cell-probe-complexity/coin-fixing-for-zero-error-cell-probe-schemes.md)

## Sources

- T. Li, J. Liang, H. Yu and R. Zhou, "Tight Cell-Probe Lower Bounds for Dynamic Succinct Dictionaries", Proceedings of the 64th IEEE Symposium on Foundations of Computer Science (FOCS), 2023; arXiv:2306.02253.
