# Add/remove differential privacy implies replace-one differential privacy

Let $U$ be a finite set, $n$ a natural number, $\varepsilon \ge 0$ and $\delta \ge 0$. For a database of $n$ rows $S : \{1, \dots, n\} \to U$, let $h(S) : U \to \mathbb{N}$ be its histogram, $h(S)(u) = \#\{i : S_i = u\}$. Let $M$ be a mechanism on histograms, mapping each $x : U \to \mathbb{N}$ to a probability distribution on a measurable output space. Suppose $M$ is $(\varepsilon, \delta)$-differentially private with respect to neighbouring histograms, meaning that $\sum_u |x(u) - y(u)| \le 1$ (the addition or removal of one record). Then the mechanism $S \mapsto M(h(S))$ on row databases is

$$
\bigl(2\varepsilon,\; (1 + e^{\varepsilon})\,\delta\bigr)\text{-differentially private}
$$

with respect to neighbouring row databases, meaning that $S$ and $S'$ differ in at most one row (the replacement of one record).

The two neighbouring relations are different, and this statement does not identify them. Replacing one record changes the histogram by two unit steps, so the privacy budget is spent twice.

Here $\varepsilon$ is assumed to be a nonnegative real and $\delta$ a nonnegative extended real, with an event bound $\Pr[M(x) \in E] \le e^{\varepsilon}\Pr[M(y) \in E] + \delta$ for all measurable events $E$. Differences between histogram counts are taken in the integers, not by truncated natural-number subtraction.

## Proof sketch

If $S = S'$ there is nothing to prove. Otherwise $S$ and $S'$ differ only at one row $i$, so $h(S') = h(S) - e_{S_i} + e_{S'_i}$, where $e_u$ is the indicator histogram of $u$. The histogram $z_1 = h(S) - e_{S_i}$ has nonnegative counts because $h(S)(S_i) \ge 1$. Both $h(S), z_1$ and $z_1, h(S')$ are neighbouring histograms. Group privacy along this chain of length two gives, for every measurable event $E$, $M(h(S))(E) \le e^{2\varepsilon} M(h(S'))(E) + (1 + e^{\varepsilon})\delta$.

## Depends on

- [Differential privacy](../differential-privacy/differentially-private.md)
- [Neighbouring histograms](../differential-privacy/histogram-adj.md)
- [Neighbouring row databases](../differential-privacy/hamming-adj.md)

## Proof depends on

- [Group privacy along a chain, approximate case](../differential-privacy/group-sum.md)

## Sources

- T. Steinke, "Composition of Differential Privacy & Privacy Amplification by Subsampling", arXiv:2210.00597v4 (2022), Section 6.2 ("Addition or Removal versus Replacement for Neighbouring Datasets"): a replacement is a removal followed by an addition, so by group privacy $(\varepsilon, \delta)$-DP for addition or removal gives $(2\varepsilon, (1 + e^{\varepsilon})\delta)$-DP for replacement.
- C. Dwork and A. Roth, *The Algorithmic Foundations of Differential Privacy*, Foundations and Trends in Theoretical Computer Science 9(3–4), 2014, Definitions 2.3 and 2.4 (histogram databases at $\ell_1$ distance one) and footnote 1 to Theorem 2.2 (approximate group privacy).
