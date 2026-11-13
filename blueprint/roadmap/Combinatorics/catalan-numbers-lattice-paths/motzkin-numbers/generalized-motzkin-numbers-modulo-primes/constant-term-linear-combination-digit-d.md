# Digit decomposition of shifted sums of constant terms modulo a prime

Let $\alpha, \beta,
\gamma$ be integers with $\alpha \ne 0$ or $\gamma \ne 0$, let $a_r$ be the constant term of
$(\alpha x^{-1} + \beta + \gamma x)^r$, let $p$ be a prime, let $h < p$ be a natural number, let
$c_0, c_1, \ldots$ be integers, and let $b_r = \sum_{i=0}^{h} c_i a_{r+i}$. Let $q, k$ be natural
numbers, let $m, n_0 < p$ be natural numbers with $m \ne p - 1$, put
$n = ((qp + m) p^k + p^k - 1) p + n_0$ (in base $p$: the digits of $q$, then $m$, then $k$ digits
$p - 1$, then $n_0$), and let $C = \min(h, p - n_0 - 1)$. Then

$$b_n \equiv a_q \Big( a_m a_{p-1}^k \sum_{i=0}^{C} c_i a_{n_0+i} +
a_{m+1} \sum_{i=p-n_0}^{h} c_i a_{i-(p-n_0)} \Big) \pmod p,$$

where the last sum is empty when $h < p - n_0$.

## Sources

- Nadav Kohen, *Density and Symmetry in the Generalized Motzkin Numbers Modulo p*, INTEGERS 26 (2026), Article A22, Lemma 1.
