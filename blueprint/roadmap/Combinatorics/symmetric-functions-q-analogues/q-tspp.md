# The $q$-TSPP theorem

Fix $n$ and let $B_n = \{0, \dots, n - 1\}^3$. A totally symmetric
plane partition in $B_n$ is a subset $\pi \subseteq B_n$ that is a lower set of $\mathbb{N}^3$ for
the componentwise order and is invariant under every permutation of the three coordinates; the
empty set is one. Let $T_n$ be the set of triples $(i, j, k) \in B_n$ with $i \le j \le k$, and
let $o(\pi)$ be the number of elements of $\pi$ in $T_n$ (the number of orbits of $\pi$ under the
permutations of the coordinates). Then, in $\mathbb{Z}[q]$,

$$
\Big(\sum_{\pi} q^{o(\pi)}\Big) \prod_{(i,j,k) \in T_n} \big(1 - q^{i+j+k+1}\big) =
\prod_{(i,j,k) \in T_n} \big(1 - q^{i+j+k+2}\big),
$$

where the sum runs over all totally symmetric plane partitions $\pi$ in $B_n$.

Coordinates start at $0$ and the denominator is cleared: with coordinates $1, \dots, n$ this is
the formula $\sum_{\pi} q^{o(\pi)} = \prod_{1 \le i \le j \le k \le n}
(1 - q^{i+j+k-1}) / (1 - q^{i+j+k-2})$ of Koutschan, Kauers and Zeilberger.

## Sources

- Koutschan, Kauers, and Zeilberger (2011), Theorem 1. DOI: 10.1073/pnas.1019186108 Via leanprover/lean-eval@38361be, problem `q_tspp`.
