# Outer regularity of Lebesgue measure

Let $\mu$ be an outer regular measure on a topological space $X$ with a σ-algebra: every measurable set $A$ satisfies
$\mu(A) = \inf\{\mu(U) : U \supseteq A,\ U \text{ open}\}$. Then this formula holds for every subset $A$ of $X$,
measurable or not, with $\mu(A)$ the outer measure $\inf\{\mu(B) : B \supseteq A \text{ measurable}\}$. By the card's
second statement, a locally finite measure on a σ-compact pseudometrizable space with its Borel σ-algebra is regular,
hence outer regular. This is the general form of the outer regularity of Lebesgue measure: Lebesgue measure on
$\mathbb{R}$ is such a measure, and taking it as $\mu$ shows that the Lebesgue outer measure of every set
$E \subseteq \mathbb{R}$, which is $m(E)$ when $E$ is Lebesgue measurable, is the infimum of the measures of the open
sets that contain $E$; the same holds on $\mathbb{R}^n$.

## Idea

For Lebesgue measure on $\mathbb{R}$ and $m(E) < \infty$, the other case being trivial, cover $E$ by intervals $I_k$
with $\sum_k |I_k| < m(E) + \varepsilon$ and enlarge each $I_k$ to an open interval of length
$|I_k| + \varepsilon 2^{-k}$; their union $U$ is open, contains $E$ and has $m(U) < m(E) + 2\varepsilon$. So the outer
measure, defined through covers by intervals, can be computed with open sets. The second statement gives the same for
every Borel measure on $\mathbb{R}^n$ that is finite on bounded sets. Outer regularity is one half of the regularity of
Radon measures. For Lebesgue measure every measurable set is also approximated from inside by compact sets, and the two
approximations are used in the proof of Lusin's theorem.

## Statements

- [Measure of a set as an infimum over open supersets](measure-eq-i-inf-is-open.md)
- [Locally finite measures on σ-compact pseudometrizable spaces are regular](of-sigma-compact-space-of-is-locally-finite-measure.md): why Lebesgue measure is outer regular.
