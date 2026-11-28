# Additivity of the integral

Let $(X, \mathcal{M}, \mu)$ be a measure space, let $f, g \colon X \to [0, \infty]$ be measurable, and let
$c \in [0, \infty)$. Then $\int (f + g) \, d\mu = \int f \, d\mu + \int g \, d\mu$ and
$\int c f \, d\mu = c \int f \, d\mu$, with arithmetic in $[0, \infty]$.

## Idea

Homogeneity follows from the definition, since multiplication by $c > 0$ matches the simple functions below $f$ with
those below $cf$. Additivity does not: the supremum over the simple functions below $f + g$ is not visibly the sum of
the two suprema. It holds for simple functions, by finite additivity of $\mu$, and passes to measurable functions
through increasing simple approximations and the monotone convergence theorem. For real and complex functions, splitting
into positive and negative parts, and into real and imaginary parts, makes the integral linear on integrable functions,
which are closed under sums and constant multiples.
For functions with values in a Banach space, as in the card's other statements, the Bochner integral is first defined on
integrable simple functions, where it is linear, and then extended to every integrable function by approximation with
simple functions in $L^1$, which keeps it linear. For an incomplete normed target the integral is zero by convention,
so linearity is immediate.

## Statements

- [Additivity and positive homogeneity of the integral](integral-nonnegative-additive-homogeneous.md)
- [Additivity of the integral when one function is measurable](lintegral-add-left.md): additivity for functions with values in $[0, \infty]$ when one of the two is measurable.
- [Additivity of the integral of integrable functions](integral-add.md): additivity extended to integrable functions, with values in a normed space.
- [Homogeneity of the integral](integral-smul.md): homogeneity for every scalar, such as a real or complex one.
- [The sum of two integrable functions is integrable](integrable-add.md): integrable functions are closed under sums, so the integral of a sum is defined.
- [A constant multiple of an integrable function is integrable](integrable-const-mul.md): integrable functions are closed under constant multiples.

## Background

- [Lebesgue integral](../lebesgue-integral/README.md): the integral
- [Monotone convergence theorem](../../monotone-convergence-theorem/README.md): used in the proof
- [Approximation by simple functions](../../approximation-by-simple-functions/README.md): used in the proof

## Sources

- S. Axler, *Measure, Integration & Real Analysis*, results 3.16, 3.20 and 3.21 (version read: the open-access PDF dated 12 June 2026).
