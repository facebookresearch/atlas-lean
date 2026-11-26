# Knockoff filter

The knockoff filter (Barber and Candès, Ann. Statist. 2015) selects relevant variables in a
regression with a finite-sample guarantee on the false discovery rate, without p-values. For each
variable $X_j$ one builds a knockoff copy $\tilde X_j$ that mimics the dependence structure of the
features but is known to be irrelevant, and computes a statistic $W_j$ that is large and positive
when $X_j$ looks more important than $\tilde X_j$ and whose sign flips when the two are swapped. For a
null variable, swapping changes nothing in distribution, so the signs of the nonzero null $W_j$ are
independent fair coins given $|W|$; a statistic equal to $0$ is never selected. The count $\#\{j : W_j \le -t\}$ then estimates the number of false
selections among $\{j : W_j \ge t\}$, and the filter selects $\{j : W_j \ge T\}$ at the first threshold
$T$ where the estimated false discovery proportion is at most $q$. With the $+1$ correction
(knockoff+) the false discovery rate is at most $q$; without it, a modified FDR is. Model-X
knockoffs (Candès, Fan, Janson and Lv, JRSSB 2018) construct the knockoffs from the known law of
$X$ ($(X, \tilde X)_{\mathrm{swap}(S)} \overset{d}{=} (X, \tilde X)$ and $\tilde X \perp Y \mid X$), for any conditional law of $Y$ given $X$, with the
nulls defined by $Y \perp X_j \mid X_{-j}$; the same coin-flip property, and hence the same theorems,
follow.

The FDR theorems below are stated for any statistics whose null signs are fair coins; the thresholds, the selected sets and the deterministic false-discovery-proportion bound are elementary.

- [Modified FDR control by knockoff](integral-card-inter-div-knockoff-selecti.md)
- [FDR control by knockoff+](integral-false-discovery-proportion-knoc.md)
- [The knockoff threshold is attained](exists-eq-of-knockoff-threshold-eq-coe.md)
- [The false discovery proportion of knockoff+ is bounded by a null-count ratio](false-discovery-proportion-knockoff-sele.md)
- [Sign flip on a set of coordinates](flip-signs.md)
- [Knockoff selected set](knockoff-selection.md)
- [Knockoff+ is more conservative than knockoff](knockoff-selection-one-subset-zero.md)
- [Knockoff threshold](knockoff-threshold.md)
- [The estimated false discovery proportion is at most $q$ at the threshold](knockoff-threshold-ratio-le.md)
- [A finite knockoff threshold is positive](pos-of-knockoff-threshold-eq-coe.md)
- [Only positive statistics are selected](pos-of-mem-knockoff-selection.md)

## Related topics

- [Benjamini–Hochberg procedure](../benjamini-hochberg-procedure/README.md): the p-value-based procedure with the same target, FDR at most $q$; knockoff+ replaces the uniform null p-values by fair null signs, and the BH step-up threshold by a sequential, stopping-time threshold.
- [Valid p-values and false discovery proportion](../valid-p-values-and-false-discovery-proportion/README.md): the false discovery proportion $|R \cap H_0| / \max(|R|, 1)$ of the knockoff guarantee.
- [Permutation tests](../permutation-tests/README.md): the other exchangeability-based route to finite-sample validity; knockoffs exploit invariance under swapping each variable with its copy.
- [Split conformal prediction](../split-conformal-prediction/README.md): exchangeability gives finite-sample guarantees for prediction too; there the test score is exchangeable with the calibration scores, for knockoffs each null statistic is invariant in law under a swap.
