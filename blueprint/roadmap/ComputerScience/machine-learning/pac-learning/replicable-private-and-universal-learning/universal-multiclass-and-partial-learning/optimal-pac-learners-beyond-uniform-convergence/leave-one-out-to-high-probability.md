# Leave-one-out bounds give optimal high-probability risk bounds for aggregated learners

Let $\hat f$ be a predictor that is symmetric in its training sample and has bounded leave-one-out error on realizable samples: for every realizable sample $S = ((x_i, y_i))_{i \le n}$ and a loss $\ell$ with values in $[0,1]$,

$$
\sum_{i=1}^{n} \ell\big(\hat f(x_i; S^{-i}), y_i\big) \le M_n,
$$

with $M_n$ nondecreasing in $n$. Then for every realizable distribution $P$ and $\delta \in (0,1)$, with probability at least $1 - \delta$ over $S \sim P^n$ (with $n/4$ an integer), the predictors trained on the prefixes $S_{\le t}$ satisfy

$$
\frac{4}{3n} \sum_{t = n/4}^{n-1} R_P\big(\hat f(\cdot; S_{\le t})\big) \le 4.82\Big(\frac{M_n}{n} + \frac{1}{n}\log\frac{2}{\delta}\Big).
$$

For classification, a majority vote over these prefix predictors therefore has error at most $9.64\big(M_n/n + \log(2/\delta)/n\big)$. Applied to the one-inclusion graph predictor of a binary class of VC dimension $d$ (where $M_n \le d$) this gives the optimal bound $9.64\big(d/n + \log(2/\delta)/n\big)$ without uniform convergence; for a multiclass class $H \subseteq Y^X$ with a finite label set $Y$, the one-inclusion hypergraph predictor has $M_n \le \lceil \mu_H(n) \rceil$, where $\mu_H(n)$ is the largest maximum density of a one-inclusion hypergraph of $H$ projected to $n$ points, and the majority vote has error at most $9.64\big(\lceil \mu_H(n) \rceil/n + \log(2/\delta)/n\big)$. For a partial concept class of VC dimension $d$ the modified one-inclusion predictor again has $M_n \le d$, which gives the bound $9.64\big(d/n + \log(2/\delta)/n\big)$, matching the worst-case lower bound for partial classes of VC dimension $d$ up to constants.

## Proof sketch

View the predictors trained on growing prefixes as an online learner: on an i.i.d. sample its expected number of mistakes is controlled through the leave-one-out bound, and online-to-batch conversion turns this into a risk bound, the key point being that the conversion still works when the mistake count is a random quantity depending on the sample. Martingale tail bounds in forward and reverse time give the exponential tail, and averaging only over the last three quarters of the prefixes avoids the $\log n$ loss that summing $M_t/t$ over all $t$ would cause. A majority vote has error at most twice the average risk of the voters.

## Depends on

- [Permutation-invariant learners and leave-one-out error](permutation-invariant-learner-leave-one-out.md)
- [One-inclusion hypergraphs, orientations and out-degree](../list-learning-and-multiclass-pseudo-cubes/one-inclusion-hypergraph.md)
- [The realizable distribution family](../../../occam-bound-for-consistent-learners/realizable-family.md)

## Proof depends on

- [Online-to-batch conversion](../../../../online-learning-and-boosting/online-to-batch-conversion.md)
- [Haussler-Littlestone-Warmuth expected error bound for the one-inclusion predictor](../../../sample-complexity-and-combinatorial-dimensions/packing-and-one-inclusion-graphs/one-inclusion-predictor-error-bound.md)

## Sources

- I. Aden-Ali, Y. Cherapanamjeri, A. Shetty, N. Zhivotovskiy, "Optimal PAC Bounds without Uniform Convergence", FOCS (2023), arXiv:2304.09167, Assumptions 2.1 and 2.3, Theorems 2.1 and 2.2, Corollaries 2.9 and 2.10, Lemmas 4.2 and 4.3.
