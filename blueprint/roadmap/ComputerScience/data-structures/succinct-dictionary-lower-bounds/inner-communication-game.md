# Inner communication game for succinct dictionaries

Let $U = n^{1+\alpha}$ for a constant $\alpha > 0$, $\gamma = \alpha/(6(1+\alpha))$, $\beta$ the absolute constant of the Bloomier-filter encoding (a set separating two given disjoint sets $A, B \subseteq [U]$ is encoded in at most $\beta(|A| + |B|)$ expected bits), and let $g, m$ be integers with $g < m/2$ and $m < n/2$. Fix a deterministic cell-probe scheme for the dynamic dictionary with at most $n$ keys of $[U]$, with cells of $w = \log_2 U$ bits and a memory of $\log_2 \binom{U}{n} + R$ bits. Let $C_{\mathrm{bef}}$ be its state before a segment of $m$ meta-operations of the insert–query–delete distribution, so that its key set $K$ is a uniform $n$-subset of $[U]$; let the segment delete a uniform $m$-subset $D \subseteq K$ in uniform order; and let $A, B$ be uniform $m$-subsets of $[U] \setminus K$ conditioned on $|A \cap B| = g$, inserted in the same uniform order. Running the segment from $C_{\mathrm{bef}}$ with insertion set $A$ (respectively $B$) gives a final state $C_A$ ($C_B$) and a set $S_A$ ($S_B$) of probed cells. Call $A$ and $B$ *consistent* if $C_A$ and $C_B$ differ in at most $\gamma m$ cells of $S_A \cap S_B$.

If $t > 0$ satisfies $\frac{1}{2} \gamma m \log_2 U \ge R + 5m + 2(\beta+1) m t$, $m \ge n^{1-\gamma/2}$ and $\mathbb{E}[|S_A|] \le m t$, then

$$
\Pr\left[A \text{ and } B \text{ are consistent} \;\middle|\; |A \cap B| = g\right] \le U^{-\gamma m}.
$$

For the insert–delete distribution of a dictionary with values independent and uniform in $[V]$, the same bound holds without queries when $U \ge 3n$, $V \ge U^{2 + 5\gamma}/n^2$ (here $\gamma > 0$ is any real), $\frac{1}{2} \gamma m \log_2 U \ge 2mt + 2R + 4m$ and $\mathbb{E}[|S_A|] \le m t$.

## Proof sketch

Alice knows $C_{\mathrm{bef}}$ and the key sequences, Bob knows only the insertion and deletion orders, and Alice must convey $A$, $B$, $D$ and $K$ when $A$ and $B$ are consistent. She sends a consistency bit, $B$, a mixed memory equal to $C_{\mathrm{bef}}$ on $S_B$ and to $C_A$ elsewhere, a Bloomier filter telling the two parts apart on $S_A \cup S_B$ (at most $2\beta m t$ expected bits), the index of $D$ among the at most $\binom{n+m}{m}$ deletion sets that pass Bob's simulation of the segment with insertions $B$ (the queries make the true $D$ pass), and the at most $\gamma m$ cells of $S_A \cap S_B$ on which $C_A$ and $C_B$ differ. Bob then recovers $C_A$ and from it $A$ and $K$. Comparing the expected message length with the entropy of $(A, B, D, K)$ bounds the probability of consistency by $U^{-\gamma m}$. In the update-only version Bob learns the stored keys and values from the memory states instead of from query answers, the long random values supplying the missing entropy.

## Depends on

- [Hard operation distributions for dynamic dictionaries](hard-operation-distributions.md)
- [Deterministic dynamic cell-probe scheme](../cell-probe-complexity/deterministic-cell-probe-scheme.md)
- [Information-theoretic space bound for dictionaries](../hashing/succinct-dictionaries-and-hash-families/dictionary-specifications/information-theoretic-dictionary-space.md)

## Proof depends on

- [Counting bound for cell-probe trees](../cell-probe-complexity/counting-bound-for-cell-probe-trees.md)

## Sources

- T. Li, J. Liang, H. Yu and R. Zhou, "Tight Cell-Probe Lower Bounds for Dynamic Succinct Dictionaries", Proceedings of the 64th IEEE Symposium on Foundations of Computer Science (FOCS), pp. 1842-1862, 2023; arXiv:2306.02253.
