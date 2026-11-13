# Park–Pham theorem on positive empirical processes

There is a real number $L > 0$ with the
following property. Let $N > 0$, let $\mathbb{T}$ be a Polish space with its Borel
$\sigma$-algebra and a probability measure $\nu$, and let $Y_1, \dots, Y_N$ be independent random
variables on a measure space $(\Omega, P)$ with values in $\mathbb{T}$, each with law $\nu$. For
$f : \mathbb{T} \to [0, \infty)$ let $Z_f = \frac{1}{N} \sum_{i=1}^{N} f(Y_i)$. Let
$\mathcal{F}$ be a finite set of measurable functions from $\mathbb{T}$ to $[0, \infty)$ that are
essentially bounded with respect to $\nu$, and write
$E = \mathbb{E}\bigl[\sup_{f \in \mathcal{F}} Z_f\bigr]$, computed in $[0, \infty]$. If
$0 < E < \infty$, then there is a finite collection $\mathcal{C}$ of pairs $(g, t)$, where
$g : \mathbb{T} \to [0, \infty)$ is measurable and $t > 0$ is real, such that every $\omega$
with $\sup_{f \in \mathcal{F}} Z_f(\omega) \ge L E$ satisfies $Z_g(\omega) \ge t$ for some
$(g, t) \in \mathcal{C}$, and $\sum_{(g, t) \in \mathcal{C}} P(Z_g \ge t) \le 1/2$.

The paper does not state explicitly that $\mathcal{C}$ is finite. It must at least be countable
for the sum to make sense, and the collections produced by the proof are finite.

## Sources

- J. Park and H. T. Pham, `On a conjecture of Talagrand on selector processes and a consequence on positive empirical processes`, Annals of Math, 199 (3) 2024. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge. Problem `annals_supremum_of_selector_processes` of the lean-eval benchmark.
