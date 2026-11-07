# TBZ-qMZVs in the SZ model

Let $w = (w_1, \dots, w_r)$ be a TBZ word: each letter is
either $\bar 1$ or a natural number $k \ge 1$, and $w_1$ is not the number $1$. Let
$U_{TBZ}(w) = \sum_v c_v\, v$ be the formal $\mathbb{Q}$-linear combination of SZ indices obtained
by replacing each letter $\bar 1$ by $1$ and each letter $k$ by $k$ or by $k - 1$, summed over all
choices. Then the Takeyama–Bradley–Zhao qMZV of $w$ is the corresponding combination of
Schlesinger–Zudilin qMZVs: $\zeta_q^{TBZ}(w) = \sum_v c_v\, \zeta_q^{SZ}(v)$.

In block form, writing $\{a\}^d$ for $d$ copies of the letter $a$: for $d_1, \dots, d_s \ge 0$ and
$k_1, \dots, k_{s-1} \ge 1$ with $k_1 \ge 2$ if $d_1 = 0$,

$$
\zeta_q^{TBZ}(\{\bar 1\}^{d_1}, k_1, \{\bar 1\}^{d_2}, \dots, k_{s-1}, \{\bar 1\}^{d_s}) =
\sum_{\delta \in \{0,1\}^{s-1}} \zeta_q^{SZ}(\{1\}^{d_1}, k_1 - \delta_1, \{1\}^{d_2}, \dots,
k_{s-1} - \delta_{s-1}, \{1\}^{d_s}).
$$

## Sources

- Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6, Proposition 9 (i) (`integers-2024-A6-prop-9`).
