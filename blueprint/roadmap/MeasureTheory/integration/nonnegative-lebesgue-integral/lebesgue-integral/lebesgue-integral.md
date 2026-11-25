# Lebesgue integral

Let $(X, \mathcal{M}, \mu)$ be a measure space. For a measurable function $f \colon X \to [0, \infty]$,
its integral with respect to $\mu$ is

$$\int f \, d\mu = \sup\Big\{ \sum_{j=1}^m c_j \, \mu(A_j) : A_1, \ldots, A_m \in \mathcal{M} \text{ disjoint},
\ c_1, \ldots, c_m \in [0, \infty),\ \sum_{j=1}^m c_j \chi_{A_j} \le f \Big\},$$

an element of $[0, \infty]$, where $0 \cdot \infty = 0$; that is, the supremum of the integrals of the nonnegative
simple functions below $f$.

For a measurable function $f \colon X \to [-\infty, \infty]$, write $f^+ = \max(f, 0)$ and $f^- = \max(-f, 0)$, which
are measurable, as are $|f|$ and, for complex $f$, $\operatorname{Re} f$ and $\operatorname{Im} f$, being continuous
functions of $f$. If at least one of $\int f^+ \, d\mu$ and $\int f^- \, d\mu$ is finite, the integral of $f$ is
$\int f \, d\mu = \int f^+ \, d\mu - \int f^- \, d\mu$. A measurable real-valued $f$ is integrable when
$\int |f| \, d\mu < \infty$, and then $\int f \, d\mu$ is a real number.

For a measurable function $f \colon X \to \mathbb{C}$ with $\int |f| \, d\mu < \infty$, the integral is
$\int f \, d\mu = \int \operatorname{Re} f \, d\mu + i \int \operatorname{Im} f \, d\mu$. For $E \in \mathcal{M}$,
$\int_E f \, d\mu$ means $\int f \chi_E \, d\mu$.

## Depends on

- [Measure](../../../measures/measures-and-countable-additivity/measures/measure.md)
- [Measurable function](../../../measurable-spaces/measurable-spaces-and-measurable-functions/measurable-functions/measurable.md)
- [Indicator function of a set](../../../../Algebra/algebraic-identities/indicator-one.md)
- [Continuous maps are Borel measurable](../../../measurable-spaces/borel-algebras-and-continuous-maps/continuous-maps-are-borel-measurable/borel-measurable.md)

## Sources

- S. Axler, *Measure, Integration & Real Analysis*, Definition 3.3 with result 3.9, and Definitions 3.18 and 6.21 (version read: the open-access PDF dated 12 June 2026).
