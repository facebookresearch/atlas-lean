# Kolmogorov's three-series theorem: sufficiency

Let $X_0, X_1, \dots$ be independent real random variables on a probability space, let $A > 0$, and let $Y_n = X_n \mathbf{1}_{\{|X_n| \le A\}}$ be the truncation of $X_n$ at $A$. If $\sum_n P(|X_n| > A) < \infty$, the series of truncated means $\sum_n \mathbb{E}[Y_n]$ converges absolutely, and $\sum_n \operatorname{Var}(Y_n) < \infty$, then the partial sums $\sum_{i < n} X_i$ converge almost surely to a finite limit. The classical theorem asks only that $\sum_n \mathbb{E}[Y_n]$ converge; this form asks that it converge absolutely.

## Idea

The three series split one hard question into three easy ones. By the first Borel–Cantelli lemma, the first series makes $X_n = Y_n$ for all large $n$ almost surely, so $\sum X_n$ and $\sum Y_n$ converge together. The truncations are bounded and independent, so the centred partial sums $\sum_{i<n} (Y_i - \mathbb{E}[Y_i])$ form a martingale whose second moments are bounded by the variance series; bounded in $L^2$, hence in $L^1$, it converges almost surely. Adding back the convergent series of means gives the convergence of $\sum Y_n$. For example, with independent fair signs $\varepsilon_n = \pm 1$, the series $\sum_{n \ge 1} \varepsilon_n / n$ converges almost surely because $\sum_n 1/n^2 < \infty$. The converse statements on this card recover the three conditions from almost-sure convergence, with the means' series convergent but not necessarily absolutely convergent.

## Statements

- [Kolmogorov's three-series theorem (sufficiency direction)](kolmogorov-three-series-sufficiency.md)
- [Kolmogorov three-series necessity, series (2)–(3)](three-series-necessity-mean-variance.md): converse direction: series (2) and (3)
- [Kolmogorov three-series theorem, necessity, first series](summable-tail-prob-of-ae-tendsto.md): converse direction: series (1)
- [Convergent series whose truncated means are not absolutely summable](summable-mean-necessity-false.md): counterexample: absolute summability of means is not necessary
- [Divergent tail probabilities prevent almost-sure convergence of partial sums](not-ae-tendsto-partial-sum-of-tsum-tail.md): contrapositive of the first necessity step: divergent tail probabilities prevent convergence
- [Three-series necessity, second half of the variance step](summable-variance-of-bounded-ae-tendsto.md): lemma for the converse (variance series)
- [Mean step of three-series necessity](tendsto-sum-integral-of-bounded-ae-tends.md): lemma for the converse (mean series)
- [Fourth-moment bound for sums of bounded independent variables](integral-pow-four-le.md): lemma for the converse: fourth-moment bound
- [Expectation of a product of independent functions factors](integral-mul-of-indep-comp.md): lemma for the converse: expectations of independent products factor
- [Pair of coordinates from two independent copies](pair-rv.md): definition used for symmetrisation in the converse
- [Symmetrized random variable](symm-rv.md): definition used for symmetrisation in the converse
- [Truncated sums converge almost surely](ae-tendsto-truncated-of-conditions.md): lemma used in the proof of the main statement
- [Almost sure convergence of centered truncated sums](ae-tendsto-centered-of-indep-summable-va.md): lemma used in the proof of the main statement
- [Almost-sure convergence of L¹-bounded sums of independent centered variables](ae-tendsto-sum-of-indep-centered-l1bdd.md): convergence of $L^1$-bounded centred independent sums
- [Eventually equal series inherit almost-everywhere convergence](ae-tendsto-of-ae-eventually-eq-and-ae-te.md): lemma used in the proof of the main statement
- [$L^1$ norm bounded by the square root of the second moment](e-lp-norm-one-le-sqrt-integral-sq.md): lemma used in the proof of the main statement
- [Truncation preserves almost-sure limits of bounded partial sums](ae-tendsto-truncated-rv-of-bdd.md): a basic fact of the truncation in the statement: for variables bounded by the cutoff it changes nothing, so the almost-everywhere convergence of their partial sums is kept

## Background

- [Truncation of random variables](../truncation/README.md)
- [Martingale convergence theorem](../../../martingales/martingale-convergence-theorems/README.md)
