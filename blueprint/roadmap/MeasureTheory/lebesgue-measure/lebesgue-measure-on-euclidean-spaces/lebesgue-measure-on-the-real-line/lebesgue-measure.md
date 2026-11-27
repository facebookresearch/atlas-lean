# Lebesgue measure on the real line

The length $\ell(I)$ of an open interval $I \subseteq \mathbb{R}$ is $b - a$ if $I = (a, b)$ with $a < b$ real, $0$ if
$I$ is empty, and $\infty$ if $I$ is unbounded. The Lebesgue outer measure of a set $A \subseteq \mathbb{R}$ is

$$m^*(A) = \inf\Big\{ \sum_{k=1}^\infty \ell(I_k) : I_1, I_2, \ldots \text{ open intervals with }
A \subseteq \bigcup_{k=1}^\infty I_k \Big\} \in [0, \infty].$$

A set $A \subseteq \mathbb{R}$ is Lebesgue measurable if there is a Borel set $B \subseteq A$ with
$m^*(A \setminus B) = 0$. Lebesgue measure is the function $m$ on the Lebesgue measurable sets given by $m(A) = m^*(A)$.

## Depends on

- [Borel σ-algebra](../../../measurable-spaces/measurable-spaces-and-measurable-functions/sigma-algebras/borel.md)

## Sources

- S. Axler, *Measure, Integration & Real Analysis*, Definitions 2.1, 2.2, 2.70 and 2.73 (version read: the open-access PDF dated 12 June 2026).
