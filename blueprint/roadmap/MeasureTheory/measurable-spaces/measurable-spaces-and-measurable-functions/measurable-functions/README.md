# Measurable functions

Let $(X, \mathcal{M})$ and $(Y, \mathcal{N})$ be measurable spaces. A function $f \colon X \to Y$ is measurable if
$f^{-1}(E) \in \mathcal{M}$ for every $E \in \mathcal{N}$. Giving $\mathbb{R}$, $[-\infty, \infty]$ or $\mathbb{C}$ its
Borel σ-algebra specializes this general definition to real-, extended-real- or complex-valued functions: such an $f$ is
measurable when $f^{-1}(B) \in \mathcal{M}$ for every Borel set $B$; a random variable is a measurable function from a
probability space to $\mathbb{R}$.

## Idea

Measurability is what makes $\int f \, d\mu$ and $\mu(\{f > t\})$ meaningful. Compositions of measurable maps are
measurable, continuous maps are measurable for Borel σ-algebras, and a real-valued $f$ is measurable as soon as
$\{f > t\} \in \mathcal{M}$ for every real $t$. Sums and products of real or complex measurable functions, suprema and
infima of sequences of extended-real ones, and pointwise limits of sequences with values in a metrizable space with its
Borel σ-algebra, such as $[-\infty, \infty]$ or $\mathbb{C}$, are measurable; the card's other statements give the
limits, suprema and infima, so the class is stable under the operations of analysis. In probability a random variable
$X \colon \Omega \to \mathbb{R}$ is a measurable map, and its law is the image of the probability measure under $X$.

## Statements

- [Measurable function](measurable.md)
- [Pointwise limits of measurable functions are measurable](measurable-of-tendsto-metrizable.md): pointwise limits of sequences, with values in a metrizable space with its Borel σ-algebra, such as $[-\infty, \infty]$ or $\mathbb{C}$.
- [Suprema of sequences of measurable functions are measurable](i-sup.md): countable suprema, with values in an ordered space such as $[0, \infty]$ or $[-\infty, \infty]$.
- [Infima of sequences of measurable functions are measurable](i-inf.md): countable infima, likewise.

## Background

- [σ-algebras](../sigma-algebras/README.md): measurable spaces

## Sources

- S. Axler, *Measure, Integration & Real Analysis*, Definitions 2.35, 2.51, 6.19 and 12.13, and result 2.53 (version read: the open-access PDF dated 12 June 2026).
- R. Durrett, *Probability: Theory and Examples*, 5th ed., Section 1.3, definition of a measurable map (version read: the author's January 2019 PDF).
