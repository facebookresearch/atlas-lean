# Peaks of 231-avoiding permutations

Let $n \ge 1$ and $k$ be natural numbers. A permutation
$\sigma$ of $\{0, \dots, n-1\}$ avoids $231$ if there are no positions $i < j < l$ with
$\sigma(l) < \sigma(i) < \sigma(j)$, and $\sigma$ has a peak at a position $i$ with
$0 < i < n - 1$ if $\sigma(i-1) < \sigma(i)$ and $\sigma(i+1) < \sigma(i)$. The number of
231-avoiding permutations of $\{0, \dots, n-1\}$ with exactly $k$ peaks is
$2^{n-2k-1} \binom{n-1}{2k} \binom{2k}{k} / (k+1)$, computed in the natural numbers: the
exponent $n - 2k - 1$ is truncated at $0$ and the division rounds down.

## Sources

- Lara Pudwell, Jacob Roth, and Teresa Wheeland, "Distributions of Statistics over Pattern-Avoiding Permutations", Journal of Integer Sequences 22 (2019), Article 19.2.6, Theorem `T:pk231`, line 228, <https://cs.uwaterloo.ca/journals/JIS/VOL22/Pudwell/pudwell6.tex>.
