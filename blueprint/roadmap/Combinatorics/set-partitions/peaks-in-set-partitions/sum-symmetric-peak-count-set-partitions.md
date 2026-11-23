# Total number of symmetric peaks over set partitions with $k$ blocks

For natural numbers
$n$ and $k$, let $P_{n,k}$ be the set of surjective restricted-growth strings of length $n$ with
letters in $\{0, \dots, k-1\}$ (these encode the partitions of $\{1, \dots, n\}$ into exactly $k$
blocks). For $w \in P_{n,k}$ let $\operatorname{sp}(w)$ be the number of symmetric peaks of $w$,
and denote by $S(a, b)$ the Stirling numbers of the second kind. Then

$$
\sum_{w \in P_{n,k}} \operatorname{sp}(w) = (k - 1)\, S(n - 1, k) +
\sum_{j=2}^{k} \binom{j}{2} \sum_{i=3}^{n-k} j^{i-3}\, S(n - i, k),
$$

where the differences $k - 1$, $n - 1$ and $n - k$ of natural numbers are truncated at $0$.

## Sources

- Walaa Asakly and Noor Kezil, *Counting Symmetric and Non-Symmetric Peaks in a Set Partition*, INTEGERS 26 (2026), Article A8, Corollary 1.
