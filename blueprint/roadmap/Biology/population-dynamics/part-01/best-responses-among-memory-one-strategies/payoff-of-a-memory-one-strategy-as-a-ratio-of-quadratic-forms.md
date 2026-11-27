# Payoff of a memory-one strategy as a ratio of quadratic forms

In the prisoner's dilemma with payoffs $T > R > P > S$ and $2R > T + S$, a **memory-one strategy** is $p = (p_1, p_2, p_3, p_4) \in [0,1]^4$, the probabilities of cooperating after the outcomes $CC, CD, DC, DD$ of the previous round (own move first). Against a memory-one opponent $q$, play is a Markov chain on $\{CC, CD, DC, DD\}$ whose transition matrix has rows

$$\big(p_i q_{\sigma(i)},\ p_i(1 - q_{\sigma(i)}),\ (1 - p_i)q_{\sigma(i)},\ (1 - p_i)(1 - q_{\sigma(i)})\big), \qquad \sigma = (1, 3, 2, 4),$$

since the opponent sees $CD$ and $DC$ swapped. With stationary vector $v$, the long-run payoff is $u_q(p) = v \cdot (R, S, T, P)$.

**Theorem 1.** There are symmetric $4 \times 4$ matrices $Q, \bar Q$ with zero diagonals, vectors $c, \bar c$ and constants $a, \bar a$, all polynomial in $q$ and the payoffs, such that

$$u_q(p) = \frac{\tfrac12\,p\,Q\,p^{\top} + c\,p + a}{\tfrac12\,p\,\bar Q\,p^{\top} + \bar c\,p + \bar a},$$

with $a = -Pq_2 + P + Tq_4$ and $\bar a = -q_2 + q_4 + 1$. Against opponents $q^{(1)}, \dots, q^{(N)}$ (a tournament), the average payoff $\frac1N\sum_i u_{q^{(i)}}(p)$ is the corresponding sum of such ratios.

**Theorem 2 (best responses).** A best response $p^* = \arg\max_{p \in [0,1]^4}\sum_{i} u_{q^{(i)}}(p)$ lies in the finite candidate set $S_q$ of points $p$ obtained, for each partition $J \cup K = \{1,2,3,4\}$, by fixing $p_j \in \{0, 1\}$ for $j \in J$ and solving $\partial_{p_k}\sum_i u_{q^{(i)}}(p) = 0$ for $k \in K$, together with the vertices $\{0,1\}^4$.

## Depends on

- [Existence of a stationary distribution](../../../../Probability/markov-chains/convergence-theorem-for-finite-markov-chains/exists-stationary.md)

## Expansion

The stationary distribution of the four-state chain is a ratio of determinants by Cramer's rule; each transition entry is affine in each $p_i$ and no product $p_i p_i$ appears in any minor, which leaves only cross terms $p_i p_j$ and gives zero diagonals. Since $u_q$ is not concave (against unconditional cooperation, $(0,0,0,0)$, $(\tfrac12, 0, 0, 0)$ and $(\tfrac12, 0, 0, \tfrac12)$ are all best responses), the maximum over the box is found by Karush–Kuhn–Tucker reasoning: on each face some coordinates sit at bounds and the others satisfy first-order conditions, a system of polynomial equations after clearing the positive denominators. Evaluating the objective on $S_q$ yields best responses that are generally not zero-determinant (extortionate) strategies, and in multi-opponent settings memory-one best responses can be outperformed by optimized strategies with longer memory.

## Sources

- N. E. Glynatsi, V. A. Knight, "Using a theory of mind to find best responses to memory-one strategies", Scientific Reports 10 (2020) 17287, Eqs. 1–12, Theorem 1 and Theorem 2, <https://doi.org/10.1038/s41598-020-74181-y>, PMCID PMC7560663.
