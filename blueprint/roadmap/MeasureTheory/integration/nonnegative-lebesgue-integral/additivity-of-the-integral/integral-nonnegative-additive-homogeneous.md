# Additivity and positive homogeneity of the integral

Let $(X, \mathcal{M}, \mu)$ be a measure space, let $f, g \colon X \to [0, \infty]$ be measurable,
and let $c \in [0, \infty)$. Then

$$\int (f + g) \, d\mu = \int f \, d\mu + \int g \, d\mu \qquad\text{and}\qquad \int c f \, d\mu = c \int f \, d\mu,$$

with arithmetic in $[0, \infty]$, where $a + \infty = \infty$, $0 \cdot \infty = 0$ and $a \cdot \infty = \infty$ for
$a > 0$.

## Proof

For $c > 0$, multiplication by $c$ is a bijection between the simple functions below $f$ and those below $cf$, and
it multiplies their integrals by $c$; so $\int cf \, d\mu = c \int f \, d\mu$. For $c = 0$ both sides are $0$. For
additivity, the integral of a nonnegative simple function $\sum_j c_j \chi_{A_j}$ with disjoint $A_j$ is
$\sum_j c_j \mu(A_j)$, by finite additivity of $\mu$, and refining two simple functions to a common partition of $X$
into measurable sets on which both are constant shows that the integral is additive on simple functions. Take
nonnegative simple functions $\varphi_k$ increasing to $f$ and $\psi_k$ increasing to $g$. Then
$\varphi_k + \psi_k$ increases to $f + g$, and the monotone convergence theorem, applied to the three sequences,
gives $\int (f + g) \, d\mu = \lim_k \int (\varphi_k + \psi_k) \, d\mu = \int f \, d\mu + \int g \, d\mu$.

## Depends on

- [Lebesgue integral](../lebesgue-integral/lebesgue-integral.md)
- [Measure](../../../measures/measures-and-countable-additivity/measures/measure.md)
- [Measurable function](../../../measurable-spaces/measurable-spaces-and-measurable-functions/measurable-functions/measurable.md)

## Proof depends on

- [Finite additivity of a measure](../../../measures/measures-and-countable-additivity/measures/measure-bi-union-finset.md)
- [Approximation of nonnegative measurable functions by simple functions](../../approximation-by-simple-functions/exists-monotone-tendsto.md)
- [Monotone convergence theorem](../../monotone-convergence-theorem/monotone-convergence-integrals.md)

## Sources

- S. Axler, *Measure, Integration & Real Analysis*, results 3.16 and 3.20 (version read: the open-access PDF dated 12 June 2026).
