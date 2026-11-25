# Almost every point is a Lebesgue point, for doubling measures

Let $X$ be a second countable pseudometric space with its Borel σ-algebra, $\mu$ a locally finite measure on $X$ that is
uniformly locally doubling, so that there are $C \ge 0$ and $r_0 > 0$ with $\mu(\bar B(x, 2r)) \le C \mu(\bar B(x, r))$
for every $x$ and every $0 < r < r_0$, and $f$ a locally integrable function on $X$ with values in a normed additive
commutative group, such as $\mathbb{R}$ or $\mathbb{C}$. Fix a real number $K$. Then for $\mu$-almost every $x$, the
averages of $\|f(y) - f(x)\|$ over $y$ in closed balls $\bar B(w_j, \delta_j)$ tend to $0$ whenever $\delta_j \to 0^+$
and eventually $x \in \bar B(w_j, K\delta_j)$, along any filter, such as a sequence. This is the general form of the
theorem that almost every point is a Lebesgue point: taking $X = \mathbb{R}$ with Lebesgue measure, $K = 1$ and the
balls $\bar B(x, t)$ centred at $x$ gives $\frac{1}{2t} \int_{x-t}^{x+t} |f(y) - f(x)| \, dy \to 0$ as $t \to 0^+$ for
almost every $x$, for every locally integrable $f$, in particular for $f \in L^1(\mathbb{R})$.

## Idea

For $f$ with values in a real Banach space, this implies the differentiation theorem, because the distance from the
average of $f$ to $f(x)$ is at most the average of $\|f - f(x)\|$. Conversely, apply the differentiation theorem to
$\|f - c\|$ for $c$ in a countable set that is dense in a set containing almost all values of $f$, which exists because
$f$ is almost everywhere strongly measurable: for almost every $x$ the averages of $\|f - c\|$ tend to $\|f(x) - c\|$
for every such $c$, and choosing $c$ close to $f(x)$ gives the claim. Every point of continuity of $f$ is a Lebesgue
point.

## Statements

- [Almost every point is a Lebesgue point, for doubling measures](ae-tendsto-average-norm-sub.md)

## Background

- [Lebesgue differentiation theorem for doubling measures](../lebesgue-differentiation-theorem/README.md): the averages of $f$

## Sources

- S. Axler, *Measure, Integration & Real Analysis*, result 4.10, for $\mathbb{R}$ (version read: the open-access PDF dated 12 June 2026).
