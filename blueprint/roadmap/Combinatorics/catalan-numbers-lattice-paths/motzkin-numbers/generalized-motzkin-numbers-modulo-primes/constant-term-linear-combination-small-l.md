# Digit formula for shifted sums of constant terms, small last digit

Let $\alpha$, $\beta$,
$\gamma$ be integers with $\alpha \ne 0$ or $\gamma \ne 0$, and let $a_r$ be the constant term of
$(\alpha x^{-1} + \beta + \gamma x)^r$. Let $c_0, c_1, c_2, \dots$ be integers, let $h$ be a natural
number, and put $b_r = \sum_{i=0}^{h} c_i a_{r+i}$. Let $p$ be a prime with $h < p$, and let $q$,
$m$, $k$, $n_0$ be natural numbers with $m < p$, $m \ne p - 1$, $n_0 < p$ and $n_0 < p - h$. If
$n = ((qp + m)p^k + p^k - 1)p + n_0$, that is, $n$ is obtained from $q$ by appending the base-$p$
digits $m$, then $k$ digits $p - 1$, then $n_0$, then

$$
b_n \equiv a_q \, a_m \, a_{p-1}^k \sum_{i=0}^{h} c_i a_{n_0+i} \pmod p
\quad \text{and} \quad
b_n \equiv a_{(n - n_0)/p} \, b_{n_0} \pmod p.
$$

## Sources

- Nadav Kohen, *Density and Symmetry in the Generalized Motzkin Numbers Modulo p*, INTEGERS 26 (2026), Article A22, Lemma 1.
