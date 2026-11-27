# Uniform integrability equivalences

Let $\mu$ be a finite measure on a measurable space
$\alpha$, let $f_n : \alpha \to \mathbb{R}$ ($n \in \mathbb{N}$) and $g : \alpha \to \mathbb{R}$ be
in $L^1(\mu)$, write $\|h\|_1 = \int |h| \, d\mu$, and suppose that $f_n \to g$ in $\mu$-measure
(for every $\varepsilon > 0$, $\mu\{x : |f_n(x) - g(x)| \ge \varepsilon\} \to 0$). Then the
following are equivalent: (1) the family $(f_n)$ is uniformly integrable, that is,
$\sup_n \|f_n\|_1 < \infty$ and the supremum of $\int_s |f_n| \, d\mu$ over all $n$ and all sets
$s \subseteq \alpha$ with $\mu(s) \le \delta$ tends to $0$ as $\delta \to 0$; (2) $f_n \to g$ in
$L^1(\mu)$, that is, $\|f_n - g\|_1 \to 0$; (3) $\|f_n\|_1 \to \|g\|_1$.

The equivalence of (1) and (2) is the Vitali convergence theorem; (3) implies (2) by Scheffé's
lemma for convergence in measure, and (2) implies (3) by the reverse triangle inequality.
