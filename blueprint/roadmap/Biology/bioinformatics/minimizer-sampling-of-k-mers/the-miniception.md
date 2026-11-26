# The Miniception minimizer construction

Fix an alphabet of size $\sigma \ge 2$ and parameters $w$, $k$ and $k_0 < k$, and put $w_0 = k - k_0$. The **Miniception** is the minimizer $(w, k, O)$ built as follows.

1. Draw a random minimizer $(w_0, k_0, O_0)$, the *seed*.
2. Let $C_0 \subseteq \Sigma^k$ be the set of charged contexts of the seed (a context of the seed has length $w_0 + k_0 = k$).
3. Let $O$ place every $k$-mer of $C_0$ before every $k$-mer outside $C_0$, with a uniformly random order inside $C_0$; the order outside $C_0$ is irrelevant.

Because $C_0$ is a universal hitting set over $k$-mers with path length $w_0$ (see [When minimizers can reach density O(1/w)](asymptotic-optimality-condition-for-minimizers.md)), every window of $w \ge w_0$ consecutive $k$-mers contains a $k$-mer of $C_0$, so the minimizer always picks from $C_0$; $O$ is a minimizer order *compatible* with that UHS.

**Theorem (density of the Miniception).** Let $w = w_0 + 1$, $k = w_0 + k_0$ and $k_0 > (3 + \epsilon)\log_\sigma (2w_0 + 2)$. Then the expected density of the Miniception is at most

$$\frac{1.67}{w} + o\!\left(\frac{1}{w}\right).$$

With, for example, $k_0 = 4\log_\sigma w_0$ one has $w \approx k$, so this is a construction with practical parameters whose guaranteed density is below the random-minimizer value $2/(w+1) + o(1/w)$. Membership of a $k$-mer in $C_0$ is decided from its $k_0$-mers, so the picked positions of a string $S$ are found in $O(k|S|)$ time with hashing, as fast as a random minimizer, without precomputing $C_0$.

For $w \approx (x - 1)k$ with $x > 2$, a dynamic program over the same recurrences (evaluated at $k = 2500$) gives density factors $D(x)$ that increase with $x$ but stay below $2$ for $2 \le x \le 8$, with $D(2) \approx 1.67$; the authors conjecture $D(x) = 2 - o(1)$ as $x$ grows.

## Depends on

- [Density of random minimizers via charged contexts](random-minimizer-density-and-charged-contexts.md)
- [When minimizers can reach density O(1/w)](asymptotic-optimality-condition-for-minimizers.md)

## Expansion

A context of the Miniception has $w + k = 2w_0 + k_0 + 1$ letters and hence $2w_0 + 2$ $k_0$-mers; under the bound on $k_0$ these are all distinct except with probability $o(1/w)$. Conditional on distinct $k_0$-mers, the random seed order makes the position of the smallest $k_0$-mer uniform, and this position determines which of the $w + 1$ $k$-mers of the context belong to $C_0$ (a $k$-mer is in $C_0$ exactly when its smallest $k_0$-mer is its first or last one). By the charged-context lemma the context is charged exactly when the $O$-minimum, a uniformly random element among the context's $C_0$ $k$-mers, is the first or the last $k$-mer. Averaging over the seed through a divide-and-conquer recurrence on the position of the minimal $k_0$-mer, with separate conditional recurrences for the events that the first or last $k$-mer is in $C_0$, yields the constant $1.67$.

## Sources

- H. Zheng, C. Kingsford and G. Marçais, "Improved design and analysis of practical minimizers", Bioinformatics 36 (Suppl. 1) (2020), Section 2.4 (Definition 7, Theorem 7, Sections 2.4.2–2.4.5) and Section 3.1, <https://doi.org/10.1093/bioinformatics/btaa472> (PMC8248892).
