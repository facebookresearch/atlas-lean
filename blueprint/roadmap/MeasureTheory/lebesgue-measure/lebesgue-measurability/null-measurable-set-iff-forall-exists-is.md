# Lebesgue measurability by outer approximation

Let $\mu$ be a measure on a topological space $X$ whose Borel sets are measurable, and suppose
that $\mu$ is outer regular ($\mu(A) = \inf\{\mu(U) : U \supseteq A \text{ open}\}$ for measurable $A$)
and $\sigma$-finite; Lebesgue measure on $\mathbb{R}^d$ is the main example. Then a set $E \subseteq X$ is null-measurable if and only if for every $\varepsilon > 0$
there is an open set $U \supseteq E$ with $\mu(U \setminus E) \le \varepsilon$.

Here $E$ is *null-measurable* when it differs from a measurable set by a subset of a null set,
which for Lebesgue measure is Lebesgue measurability; $\mu(A)$ for a non-measurable $A$ is the
outer measure.

For Lebesgue measure on $\mathbb{R}^d$ this says that Tao's definition of Lebesgue measurability
(Definition 1.2.2, Littlewood's first principle: "every measurable set is nearly open") agrees
with null-measurability for Lebesgue measure. By
[Vitali's theorem](../../measures/vitali-set/vitali-nonmeasurable.md), some subset of $\mathbb{R}$ admits no
such approximation.

## Background

- [Vitali's theorem](../../measures/vitali-set/vitali-nonmeasurable.md): background; the non-measurable set it
  provides is one for which open outer approximation fails.

## Sources

- T. Tao, *An Introduction to Measure Theory*, Graduate Studies in Mathematics 126, American Mathematical Society, 2011, Definition 1.2.2 and Exercise 1.2.7 (i) if and only if (ii).
