# Lebesgue differentiation theorem for doubling measures

Let $X$ be a second countable pseudometric space with its Borel σ-algebra, $\mu$ a locally finite measure on $X$ that is
uniformly locally doubling, so that there are $C \ge 0$ and $r_0 > 0$ with $\mu(\bar B(x, 2r)) \le C \mu(\bar B(x, r))$
for every $x$ and every $0 < r < r_0$, and $f$ a locally integrable function on $X$ with values in a real Banach space
such as $\mathbb{R}$ or $\mathbb{C}$. Fix a real number $K$. Then for $\mu$-almost every $x$, the averages of $f$ over
closed balls $\bar B(w_j, \delta_j)$ tend to $f(x)$ whenever $\delta_j \to 0^+$ and eventually
$x \in \bar B(w_j, K\delta_j)$, along any filter, such as a sequence. This is the general form of the Lebesgue
differentiation theorem: taking $X = \mathbb{R}$ with Lebesgue measure, $K = 1$ and the balls $\bar B(x, t)$ centred at
$x$ gives $\frac{1}{2t} \int_{x-t}^{x+t} f \to f(x)$ as $t \to 0^+$ for almost every $x$, for every locally integrable
$f$, and on $\mathbb{R}^n$ the same for averages over closed balls.

## Idea

The key estimate is a maximal inequality: for integrable $f$, the set of points where the average of $\|f\|$ over some
small ball containing the point exceeds $t$ has measure at most $C' \|f\|_1 / t$, proved by a Vitali covering argument
that uses the doubling property. The theorem is clear for continuous $f$; integrable continuous functions are dense in
$L^1(\mu)$ for such a measure, and the maximal inequality controls the error of the approximation. Lebesgue measure on
$\mathbb{R}^n$ is doubling, with $C = 2^n$. Applied to an indicator function, the theorem gives Lebesgue's density
theorem. It follows from the stronger statement that almost every point is a Lebesgue point of $f$.

## Statements

- [Lebesgue differentiation theorem for doubling measures](ae-tendsto-average.md)

## Sources

- S. Axler, *Measure, Integration & Real Analysis*, result 4.21, for $\mathbb{R}$ (version read: the open-access PDF dated 12 June 2026).
