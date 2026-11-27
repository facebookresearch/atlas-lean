# Polynomial-time exact parent-set search under the MIT score

In the setting of the [MIT score for $d$-th order DBNs](mutual-information-test-score-for-high-order-dynamic-bayesian-networks.md) with $n$ variables of $k$ states each, recast the score of node $X_i$ as a cost to be minimized,

$$s(Pa_i) = v(Pa_i) + u(|Pa_i|), \qquad v(Pa_i) = 2 N_e \log k - 2 N_e\, I_s(X_i, Pa_i) \ \ge 0, \qquad u(p) = \sum_{j=1}^{p} \chi_{\alpha, (k-1)^2 k^{j-1}},$$

so that minimizing $\sum_i s(Pa_i)$ is equivalent to maximizing the MIT score (Proposition 1 of the source; the constant $2N_e \log k$ bounds $2N_e I_s(X_i, X^d)$ because mutual information is at most the entropy). Consider the search (Algorithm 1, GlobalMIT+): start with $Pa_i = \emptyset$; for $p = 1, 2, \dots, nd$, stop if $u(p) \ge s(Pa_i)$; otherwise let $P$ minimize $s$ over all $p$-subsets of $X^d$ and replace $Pa_i$ by $P$ if $s(P) < s(Pa_i)$.

**Theorem (Theorems 1 and 2 of the source).**

1. Applied to every variable, the search returns a globally optimal $d$-th order DBN under the MIT score.
2. Let $p^* = \min\{ p : u(p) \ge 2 N_e \log k \}$, which depends only on $\alpha$, $k$ and $N_e$. The search scores at most the $O\big((nd)^{p^*}\big)$ parent sets of size below $p^*$, so its worst-case running time is polynomial in the number of genes $n$ and the order $d$. For $\alpha \ge 0.6827$, where $\chi_{\alpha,l} \ge l$ for every $l$, under-estimating each quantile by the mean $l$ of the $\chi^2(l)$ law gives $p^* \le \log_k \frac{2 N_e \log k}{k - 1} + 1$, that is, a bound of order $(nd)^{\log_k N_e}$.

## Expansion

The proof is a pruning argument. Since $v \ge 0$ and $u$ is non-decreasing in the size, every parent set $P$ with $|P| \ge p$ has $s(P) \ge u(|P|) \ge u(p)$; once $u(p)$ exceeds the best cost found so far, no larger set can improve on it. The empty set has cost $s(\emptyset) = 2 N_e \log k$, so the loop always stops by $p = p^*$. Inter-slice edges make acyclicity automatic, and additivity lets each node be searched independently and in parallel, unlike the static Bayesian network case where acyclicity couples all parent choices. The price of the model class is that instantaneous regulation within a time slice is not represented; the source argues that for smooth, densely sampled expression profiles a one-step delay loses little mutual information.

## Depends on

- [Mutual information test score for high-order dynamic Bayesian networks](mutual-information-test-score-for-high-order-dynamic-bayesian-networks.md)
- [Chi-square distribution](../../../../Probability/distributions/continuous/chi-square-distribution/chi-square-measure.md)

## Sources

- N. X. Vinh, M. Chetty, R. Coppel and P. P. Wangikar, *Gene regulatory network modeling via global optimization of high-order dynamic Bayesian network*, BMC Bioinformatics 13 (2012), 131. DOI: <https://doi.org/10.1186/1471-2105-13-131>. PMCID: PMC3433362.
