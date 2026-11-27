# Cell-probe lower bound Ω(k) for dynamic dictionaries with n·log^(k) n redundancy

For every $\alpha > 0$, $\kappa \ge 1 + \alpha$, $c_R \ge 0$ and $c_w \ge 0$ there are constants $c > 0$ and $n_0$ such that the following holds for all $U, V, n, k$ with $n \ge n_0$, $4n \le U$, $n^{1+\alpha} \le U$, $V \ge 1$, $UV \le n^{\kappa}$ and $1 \le k \le \log^* n$. Let a deterministic step-indexed or zero-error randomized cell-probe scheme with $S$ cells of $w \le c_w(\log_2 U + \log_2 V)$ bits implement the dynamic dictionary with at most $n$ keys exactly on all admissible histories of length at most $4n+1$, using

$$
S w \le \log_2 \binom{U}{n} + n \log_2 V + c_R \cdot n \cdot \max(\log^{(k)} n, 1)
$$

bits. Then, for $V = 1$, its expected total number of probes on the insert–query–delete distribution ($4n$ operations), which is then the hard distribution (Distribution 1, Section 3) of Li, Liang, Yu and Zhou, is at least $c \cdot n \cdot k$; for $V \ge 1$, there is an admissible history of at most $4n$ operations on which its expected total number of probes is at least $c \cdot n \cdot k$. In particular, with $O(n)$ bits of redundancy every such scheme makes $\Omega(\log^* n)$ expected probes per operation, amortized over such a history.

## Proof sketch

For key-only dictionaries ($V = 1$) and words of $\log_2 U$ bits, build the meta-operation tree with block sizes $m_\ell = c' n \log^{(k)} n / \log^{(\ell)} n$, which has $\Omega(k)$ levels at which the outer lemma applies with $t = \Theta(\log U)$. At each such level, either half of the nodes have many attributed probes, or half of them make $\Omega(m_\ell \log U)$ probes; aggregating gives $\Omega(nk)$ expected probes in the first case for every level and $\Omega(n \log U) = \Omega(nk)$ in the second. Values are handled by the source's key-value reduction (Section 7, Theorem 7.2), which runs the key-only distribution on the universe $[UV]$: each key of $[UV]$ is split into a key of $[U]$ and a value of $[V]$, the expected $O(n^2/U)$ keys whose $[U]$-parts collide go to a side table, and the key-value scheme so yields a key-only scheme on $[UV]$ with $o(n)$ extra redundancy and $O(1)$ extra expected probes per operation, which a smaller $c$ absorbs since every insertion that changes the stored set makes at least one probe; this is why $UV$ must stay polynomial in $n$, and why for $V > 1$ the bound is on the histories this reduction feeds to the scheme rather than on the key-value distribution itself. Words of $O(\log U + \log V)$ bits change the bound by a constant factor. Coin fixing transfers the bound from deterministic step-indexed schemes to zero-error randomized ones.

## Depends on

- [Deterministic dynamic cell-probe scheme](../cell-probe-complexity/deterministic-cell-probe-scheme.md)
- [Randomized cell-probe scheme with private coins](../cell-probe-complexity/randomized-cell-probe-scheme.md)
- [Hard operation distributions for dynamic dictionaries](hard-operation-distributions.md)
- [Information-theoretic space bound for dictionaries](../hashing/succinct-dictionaries-and-hash-families/dictionary-specifications/information-theoretic-dictionary-space.md)
- [Iterated logarithm and log-star](../hashing/succinct-dictionaries-and-hash-families/dictionary-specifications/iterated-logarithm.md)

## Proof depends on

- [Outer lemma: each tree node forces many attributed probes or many probes](outer-lemma.md)
- [Meta-operation tree and probe attribution](meta-operation-tree.md)
- [Aggregating level bounds over the meta-operation tree](aggregating-level-bounds.md)
- [Coin fixing for zero-error randomized cell-probe schemes](../cell-probe-complexity/coin-fixing-for-zero-error-cell-probe-schemes.md)

## Sources

- T. Li, J. Liang, H. Yu and R. Zhou, "Tight Cell-Probe Lower Bounds for Dynamic Succinct Dictionaries", Proceedings of the 64th IEEE Symposium on Foundations of Computer Science (FOCS), pp. 1842-1862, 2023; arXiv:2306.02253.
