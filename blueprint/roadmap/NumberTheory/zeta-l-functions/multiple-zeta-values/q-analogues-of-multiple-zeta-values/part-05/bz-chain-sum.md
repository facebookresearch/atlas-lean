# Weighted chain sums

Let $o_1, \dots, o_\ell$ be a word of markers, each either a natural
number (a weighted position) or a blank (an unweighted position); let $W$ be the set of weighted
positions and $k_t$ the number at position $t \in W$. For natural numbers $M$ and $R$, the
weighted chain sum of the word at bound $M$ and target $R$ is the natural number

$$\sum \prod_{t \in W} \binom{j_t}{k_t},$$

the sum running over strictly decreasing chains $M > a_1 > a_2 > \dots > a_\ell > 0$ of natural
numbers and multiplicities $j_1, \dots, j_\ell \ge 0$ with $a_1 j_1 + \dots + a_\ell j_\ell = R$.
For the empty word ($\ell = 0$) the sum has a single empty term, so the value is $1$ if $R = 0$
and $0$ otherwise, whatever $M$ is.

## Sources

- Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6, Theorem 1 (the sums over `m₁ > n₁ > ⋯ > m_r > ⋯ > 0` with multiplicities `j, i ≥ 0`).
