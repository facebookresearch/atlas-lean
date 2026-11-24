# Empirical distribution of a type agrees with the empirical measure

Let $\alpha$ be a finite alphabet in which every singleton is measurable, $x_0, x_1, \dots$ a sequence of
letters and $n \ge 1$. The [empirical distribution](empirical.md) of the type of $(x_0, \dots, x_{n-1})$ gives
each letter $a$ the mass $\frac1n \sum_{i<n} \delta_{x_i}(\{a\})$ that the empirical measure of the first $n$
sample points gives to $\{a\}$. This bridge connects the finite, counting form of Sanov's theorem on this
topic to the measure-theoretic form used by the general theorem.

## Background

- [Empirical measure of a sample](../../../Probability/large-deviations/sanov-s-theorem/sample-empirical-measure.md):
  the definition being matched.

## Sources

- I. Csiszár, "The method of types", *IEEE Trans. Inform. Theory* 44(6) (1998), 2505–2523, Section II (the type as a relative frequency).
- S. R. S. Varadhan, *Large Deviations*, lecture notes, New York University, Spring 2010, Section 3
  (the empirical measure).
