# Convergence in measure with converging L¹ norms implies uniform integrability

Let $\mu$
be a measure on a measurable space $\alpha$, let $f_n : \alpha \to \mathbb{R}$ ($n \in \mathbb{N}$)
and $g : \alpha \to \mathbb{R}$ be in $L^1(\mu)$, and write $\|h\|_1 = \int |h| \, d\mu$. If
$f_n \to g$ in $\mu$-measure (for every $\varepsilon > 0$,
$\mu\{x : |f_n(x) - g(x)| \ge \varepsilon\} \to 0$) and $\|f_n\|_1 \to \|g\|_1$, then the family
$(f_n)$ is uniformly integrable: $\sup_n \|f_n\|_1 < \infty$, and the supremum of
$\int_s |f_n| \, d\mu$ over all $n$ and all sets $s \subseteq \alpha$ with $\mu(s) \le \delta$
tends to $0$ as $\delta \to 0$.

The proof combines the $L^1$ convergence $\|f_n - g\|_1 \to 0$ given by Scheffé's lemma for
convergence in measure with the Vitali convergence theorem.
