# Noisy evaluations

Let $(\mathcal X, \mathcal A)$ be a measurable space and $\nu$ a Markov kernel from $\mathcal X$ to $[0, 1]$: for every
$x \in \mathcal X$, $\nu_x$ is a probability measure on the Borel sets of $[0, 1]$, and $x \mapsto \nu_x(E)$ is
measurable for every Borel set $E$. An *evaluation* at $x$ returns a *reward* drawn from $\nu_x$. The *mean-payoff
function* is

$$
f(x) = \int_{[0, 1]} y \, d\nu_x(y),
$$

a measurable function with values in $[0, 1]$, and $f^* = \sup_{\mathcal X} f$.

A *strategy* with budget $n \ge 1$ is a sequence of probability kernels $\pi_1, \dots, \pi_n$, where $\pi_t$ goes from
the histories $(x_1, y_1, \dots, x_{t-1}, y_{t-1}) \in (\mathcal X \times [0, 1])^{t-1}$ to $\mathcal X$ ($\pi_1$ is a
probability measure on $\mathcal X$). The *interaction* of the strategy with $\nu$ is the probability measure
$\mathbb P$ on $(\mathcal X \times [0, 1])^n$, with coordinates $X_1, Y_1, \dots, X_n, Y_n$, obtained by composing the
kernels in this order: with $H_{t-1} = (X_1, Y_1, \dots, X_{t-1}, Y_{t-1})$, the point $X_t$ has conditional law
$\pi_t(H_{t-1})$ given $H_{t-1}$, and the reward $Y_t$ has conditional law $\nu_{X_t}$ given $(H_{t-1}, X_t)$. So each
reward is drawn, given the past and the evaluated point, independently of the past, with conditional mean
$\mathbb E[Y_t \mid H_{t-1}, X_t] = f(X_t)$. A strategy is deterministic when every $\pi_t(h)$ is the Dirac mass at a
point $s_t(h)$, for measurable maps $s_t$.

For a finite set $\mathcal X$ with all its subsets measurable, this is the
[canonical bandit model](../../stochastic-k-armed-bandits-canonical-history-law-and-regret.md) of a stochastic bandit
with arms $\mathcal X$ and rewards in $[0, 1]$. The paper on StoSOO assumes $\lvert r_t \rvert \le 1$ and the
conditional mean $\mathbb E[r_t \mid x_t] = f(x_t)$; rewards are taken in $[0, 1]$ here, as in the paper on HOO and in
the monograph.

## Sources

- S. Bubeck, R. Munos, G. Stoltz and Cs. Szepesvári, *X-armed bandits*, Journal of Machine Learning Research 12
  (2011), 1655–1695, <https://jmlr.org/papers/v12/bubeck11a.html>, Section 2.
- T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020 (author copy), Section 4.7
  (the canonical bandit model for uncountable action sets: the environment and the policy as probability kernels, the
  interaction law by the Ionescu-Tulcea theorem), whose rewards in $[0, 1]$ are the case above.
  <https://tor-lattimore.com/downloads/book/book.pdf>
- M. Valko, A. Carpentier and R. Munos, *Stochastic simultaneous optimistic optimization*, Proceedings of the 30th
  International Conference on Machine Learning (ICML 2013), PMLR 28, <https://proceedings.mlr.press/v28/valko13.html>,
  Section 1, equation (1), and Section 4.
- R. Munos, *From Bandits to Monte-Carlo Tree Search: The Optimistic Principle Applied to Optimization and Planning*,
  Foundations and Trends in Machine Learning 7(1), 2014, 1–129 (HAL hal-00747575v5,
  <https://hal.science/hal-00747575v5>), Sections 3.4 and 4.2.
