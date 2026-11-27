# Consistency of the truncating adaptive lasso

**Hypotheses.** In the [truncating lasso estimator](truncating-lasso-estimator-of-a-graphical-granger-model.md) of a graphical Granger model with $p$ genes, let $s$ be the total number of true edges and $\mathrm{pa}_i$ the set of true regulators of gene $i$. Assume, as $n \to \infty$:

1. $p = p(n) = O(n^a)$ for some $a > 0$ and $|\mathrm{pa}_i| = O(n^b)$ with $s\,n^{2b-1}\log n = o(1)$;
2. there is $\nu > 0$ with $\operatorname{Var}(X^T_i \mid X^{T-d:T-1}_{1:p}) \ge \nu$ for all $n$ and $i$;
3. there are $\delta > 0$ and $\xi > b$ such that every partial correlation $\pi_{ij}$ between $X_i$ and a true regulator $X_j$ satisfies $|\pi_{ij}| \ge \delta n^{-(1-\xi)/2}$;
4. $\lambda \asymp n^{-(1-\zeta)/2}$ for some $b < \zeta < \xi$, the adaptive weights come from an initial lasso fit, and $\Psi^t = g\exp\big(n\,\mathbb{1}\{\|A^{(t-1)}\|_0 < p^2\beta/(T-t)\}\big)$ for a large constant $g$ (that is, $M = g e^n$);
5. the number of true causal effects diminishes with the lag.

**Theorem.** Then (i) with probability tending to $1$ no false Granger-causal effect is included and the signs of the included effects are correct; (ii) with probability asymptotically at least $1 - \beta$ the true Granger-causal effects and the order of the autoregression are correctly determined.

## Expansion

For $\beta = 0$ the penalty never truncates, the estimator is the adaptive lasso on the time-ordered DAG, and variable-selection and sign consistency follow from the corresponding high-dimensional DAG result; since $\beta$ does not affect false positives this gives (i). For $\beta > 0$, let $t_0$ be the first lag with fewer than $p^2\beta/(T-t_0)$ estimated edges. By the KKT conditions a coefficient at lag $t \ge t_0$ enters only if $|2n^{-1}(\mathcal{X}^t_j)^\top(\mathcal{X}^T_i - \mathcal{X}^t\theta^t)| > \Psi^t\lambda w^t_j$; the left side grows polynomially in $n$ while $\Psi^t$ grows exponentially, so all such coefficients vanish, and the diminishing-effects assumption bounds the true edges lost there by $\beta$. Overestimating the order requires a true edge to be missed before $t_0$, which the adaptive lasso does only with exponentially small probability.

## Depends on

- [Truncating lasso estimator of a graphical Granger model](truncating-lasso-estimator-of-a-graphical-granger-model.md)

## Sources

- Shojaie A, Michailidis G, "Discovering graphical Granger causality using the truncating lasso penalty", Bioinformatics (2010), Appendix A, Theorem (Consistency of Truncating Adaptive Lasso) and its proof, <https://doi.org/10.1093/bioinformatics/btq377>, PMCID PMC2935442.
