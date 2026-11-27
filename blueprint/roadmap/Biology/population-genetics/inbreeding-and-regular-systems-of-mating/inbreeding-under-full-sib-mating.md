# Inbreeding under repeated full-sib mating

In a line maintained by repeated full-sib mating (in each generation one female and one male, full
sibs, are the parents of the next generation; no selection), let $h_t$ be the probability that the two
gene copies of one individual of generation $t$ are not identical by descent, and $k_t$ the probability
that a random gene copy of the female and a random gene copy of the male of generation $t$ are not
identical by descent, both relative to a fixed base population, with given values $h_0, k_0 \in [0, 1]$
in generation $0$. Then for $t \ge 1$

$$h_t = k_{t-1}, \qquad k_t = \tfrac14 h_{t-1} + \tfrac12 k_{t-1},$$

so $k_t = \tfrac12 k_{t-1} + \tfrac14 k_{t-2}$ for $t \ge 2$. With
$\lambda_\pm = (1 \pm \sqrt 5)/4$, the roots of $\lambda^2 - \lambda/2 - 1/4 = 0$,

$$k_t = A \lambda_+^t + B \lambda_-^t, \qquad A = \frac{k_1 - \lambda_- k_0}{\lambda_+ - \lambda_-}, \quad
B = \frac{\lambda_+ k_0 - k_1}{\lambda_+ - \lambda_-}, \quad k_1 = \tfrac14 h_0 + \tfrac12 k_0 .$$

If $h_0, k_0 \ge 0$ are not both $0$, then $A > 0$, $k_t / \lambda_+^t \to A$ and
$h_t / \lambda_+^t \to A / \lambda_+$; in particular the panmictic index $1 - F_t = h_t$ tends to $0$ at the
asymptotic rate $\lambda_+ = (1 + \sqrt 5)/4 \approx 0.809$ per generation. The decrease need not be
monotone from arbitrary founder values: $h_0 = 0$, $k_0 = 1$ gives $h_1 = 1$. When the founders are
non-inbred and unrelated relative to the base population, $h_0 = k_0 = 1$.

## Sources

- J. Felsenstein, *Theoretical Evolutionary Genetics* (GENOME 562 course text, University of Washington, version of December 2019), <https://felsenst.github.io/pgbook/pgbook.pdf>, Section V.10 "Regular Systems of Inbreeding: Full Sib Mating", equations (V-26)–(V-31),
  pp. 234–236.
