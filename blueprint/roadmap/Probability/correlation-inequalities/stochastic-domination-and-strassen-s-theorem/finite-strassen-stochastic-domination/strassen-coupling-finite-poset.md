# Strassen's theorem on a finite poset

Let $\alpha$ be a finite partially ordered set and let
$p, q : \alpha \to \mathbb{R}$ be probability mass functions, that is, nonnegative functions with
$\sum_{x \in \alpha} p(x) = 1$ and $\sum_{x \in \alpha} q(x) = 1$. Then
$\sum_{x \in U} p(x) \le \sum_{x \in U} q(x)$ for every upper set $U \subseteq \alpha$ if and only
if there is a function $\pi : \alpha \times \alpha \to \mathbb{R}$ such that $\pi(x, y) \ge 0$
for all $x, y \in \alpha$, $\sum_{y \in \alpha} \pi(x, y) = p(x)$ for every $x \in \alpha$,
$\sum_{x \in \alpha} \pi(x, y) = q(y)$ for every $y \in \alpha$, and $\pi(x, y) = 0$ whenever
$x \not\le y$.

## Sources

- V. Strassen, "The Existence of Probability Measures with Given Marginals", Ann. Math. Statist. 36 (1965), 423-439, DOI 10.1214/aoms/1177700153.
