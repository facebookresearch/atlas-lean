# Worpitzky identity for multiset permutations

Let $m$ and $x$ be natural numbers, let
$k_1, \dots, k_m$ be natural numbers with sum $K = k_1 + \dots + k_m$, and for $p \ge 1$ let
$a_p$ be the number of words $w_1 w_2 \cdots w_K$ over the alphabet $\{1, \dots, m\}$ in which
each letter $i$ occurs exactly $k_i$ times and which have exactly $p - 1$ descents, that is,
indices $j$ with $1 \le j < K$ and $w_j > w_{j+1}$. Then

$$\prod_{i=1}^{m} \binom{x + k_i - 1}{k_i} = \sum_{p=1}^{\max(1, K)} \binom{x + K - p}{K} a_p.$$

Here subtraction of natural numbers is truncated at $0$.

## Sources

- A. Dzhumadil'daev and D. Yeliussizov, *Power Sums of Binomial Coefficients*, Journal of Integer Sequences 16 (2013), Article 13.1.4, Theorem Worpitzky, lines 212-217, <https://cs.uwaterloo.ca/journals/JIS/VOL16/Yeliussizov/dzhuma6.tex>, quoting A. S. Dzhumadil'daev, *Worpitzky identity for multipermutations*, Mat. Zametki 90 (2011), 464-466.
