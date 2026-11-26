# Duality for TBZ-qMZVs

Let $w$ be a TBZ word: each letter is either $\bar 1$ or a natural
number $k \ge 1$, and the first letter is not the number $1$. Let $U_{TBZ}(w) = \sum_v c_v\, v$ be
the formal $\mathbb{Q}$-linear combination of SZ indices obtained by replacing each letter $\bar 1$
by $1$ and each letter $k$ by $k$ or by $k - 1$, summed over all choices. For an SZ index
$u = (u_1, \dots, u_s)$ of natural numbers, let $V_{TBZ}(u) = \sum_x d_{u,x}\, x$ be the formal
$\mathbb{Q}$-linear combination of TBZ words obtained by replacing each letter $u_i = 0$ by
$z_1 - z_{\bar 1}$ and each letter $u_i \ge 1$ by $\sum_{j=1}^{u_i} (-1)^{u_i - j} z_{j'}$, where
$z_a$ is the one-letter word $a$, $j' = \bar 1$ for $j = 1$ and $j' = j$ otherwise, and
multiplying out by concatenation of words. Then the Takeyama–Bradley–Zhao qMZVs satisfy

$$
\zeta_q^{TBZ}(w) = \sum_v c_v \sum_x d_{v^\dagger, x}\, \zeta_q^{TBZ}(x),
$$

where $v^\dagger$ is the SZ dual index of $v$; that is,
$\zeta_q^{TBZ} = \zeta_q^{TBZ} \circ V_{TBZ} \circ \tilde\tau \circ U_{TBZ}$ on such words, where
$\tilde\tau$ is the dual-index map and $V_{TBZ}$, $\tilde\tau$ and $\zeta_q^{TBZ}$ are extended
$\mathbb{Q}$-linearly.

## Sources

- Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6, Proposition 8 (after Takeyama).
