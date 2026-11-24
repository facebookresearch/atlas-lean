# Counting Boolean factor pairs with a small sumset

Let $n$ and $k$ be natural numbers with
$0 < k \le n$, and let $d > 0$ be a real number. Then the number of pairs $(A, B)$ of finite sets
of natural numbers such that $0 \in A$, the largest element of $A$ is $k$, the largest element of
$B$ is $n - k$, and $|A + B| \le |A| + |B| + d$, where $A + B = \{a + b : a \in A, b \in B\}$ is
the sumset, is at most $n^{2d+2} 2^k$.

This is Lemma 19 for Boolean polynomials $f$ and $g$ recorded by their supports $A$ and $B$: the
conditions say that $f$ has nonzero constant term, $\deg f = k$ and $\deg g = n - k$, and the
support of their max-min product $f \otimes g$ is $A + B$.

## Sources

- Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7, Lemma 19 (`jis-2025-25.2.7-lem-19`).
