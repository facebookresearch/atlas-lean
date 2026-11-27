# Outer approximation by open sets

Let $\mu$ be a measure on a topological space $X$ whose Borel sets are measurable, and suppose
that $\mu$ is outer regular ($\mu(A) = \inf\{\mu(U) : U \supseteq A \text{ open}\}$ for measurable $A$)
and $\sigma$-finite; Lebesgue measure on $\mathbb{R}^d$ is the main example. If $E \subseteq X$ is null-measurable, then for every $\varepsilon > 0$ there is an
open set $U \supseteq E$ with $\mu(U \setminus E) \le \varepsilon$. The set $E$ may have infinite
measure.

Here $E$ is *null-measurable* when it differs from a measurable set by a subset of a null set,
which for Lebesgue measure is Lebesgue measurability; $\mu(A)$ for a non-measurable $A$ is the
outer measure.

Proof: take a measurable $T \subseteq E$ with $\mu(E \setminus T) = 0$; cover the null set
$E \setminus T$ by an open set of measure at most $\varepsilon/2$; split $T$ along a sequence of
sets of finite measure exhausting $X$ and approximate the $n$-th piece with error at most
$\varepsilon_n$, where $\sum_n \varepsilon_n \le \varepsilon / 2$.

## Sources

- T. Tao, *An Introduction to Measure Theory*, Graduate Studies in Mathematics 126, American Mathematical Society, 2011, Lemma 1.2.13 and Exercise 1.2.7 (i) implies (ii).
