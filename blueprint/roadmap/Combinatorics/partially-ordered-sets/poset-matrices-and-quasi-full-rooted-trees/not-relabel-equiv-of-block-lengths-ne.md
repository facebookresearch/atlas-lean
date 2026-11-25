# Direct sum criterion for relabeling inequivalence

Let $n, t \ge 2$ and let
$M$ and $M'$ be poset matrices of order $n$, Boolean matrices with rows and columns indexed by
$0, \dots, n - 1$. Let $0 = l_0 < l_1 < \dots < l_t = n$ be such that the gaps $l_{k+1} - l_k$ are
nondecreasing in $k$. Suppose that for every $k \le t$, $M_{ij}$ is false for all $i < l_k \le j$,
and that for every $k < t$ there is $s \ge 1$ with $l_k + s < l_{k+1}$ such that $M_{ij}$ is true
for all $i, j$ with $l_k \le i < l_k + s \le j < l_{k+1}$. Suppose the same of $M'$ with a sequence
$0 = l'_0 < l'_1 < \dots < l'_t = n$ whose gaps are nondecreasing. If $l_k \ne l'_k$ for some $k$,
then $M$ and $M'$ are not relabeling equivalent: there is no permutation $\sigma$ of
$\{0, \dots, n - 1\}$ with $M'_{ij} = M_{\sigma(i) \sigma(j)}$ for all $i, j$.

The source assumes in addition that $M$ and $M'$ represent quasi-full $t$-ary rooted forests; the
statement holds without that assumption.

## Sources

- Salah Uddin Mohammad, Md. Shah Noor, and Md. Rashed Talukder, *Recognition and Enumeration of the Quasi-Full Rooted Trees*, Journal of Integer Sequences 28 (2025), Article 25.6.3, Theorem 11 (`jis-2025-25.6.3-thm-11`).
