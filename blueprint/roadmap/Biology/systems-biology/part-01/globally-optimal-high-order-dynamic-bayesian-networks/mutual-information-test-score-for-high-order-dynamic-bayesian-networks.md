# Mutual information test score for high-order dynamic Bayesian networks

Let $X_1, \dots, X_n$ be discretized gene expression variables observed as $m$ time series of lengths $N_1, \dots, N_m$, with $r_i$ states for $X_i$. A **$d$-th order dynamic Bayesian network** (DBN) with only inter-time-slice edges assigns to each $X_i[t]$ a parent set

$$Pa_i = \{ X_{i_1}[t - \delta_{i1}], \dots, X_{i_{s_i}}[t - \delta_{i s_i}] \}, \qquad 1 \le \delta_{ij} \le d,$$

a subset of $X^d = X[t-1] \cup \dots \cup X[t-d]$. Let $I_s(X_i, Pa_i)$ be the empirical **time-delayed mutual information**, computed after shifting the target forward by $d$ steps and each parent forward by $d - \delta_{ij}$ steps, so that only aligned samples within a single series are used; the number of effective observations is

$$N_e = \sum_{l=1}^{m} N_l - m d.$$

The **MIT score** of the DBN $G$ on data $D$ is

$$S_{MIT}(G : D) = \sum_{i \,:\, Pa_i \ne \emptyset} \left( 2 N_e\, I_s(X_i, Pa_i) - \sum_{j=1}^{s_i} \chi_{\alpha,\, l_{i\sigma_i(j)}} \right),$$

where $\chi_{\alpha, l}$ is the $\alpha$-quantile of the $\chi^2(l)$ distribution, the parents are ordered by a permutation $\sigma_i$ with non-increasing numbers of states, and

$$l_{i\sigma_i(1)} = (r_i - 1)(r_{i\sigma_i(1)} - 1), \qquad l_{i\sigma_i(j)} = (r_i - 1)(r_{i\sigma_i(j)} - 1) \prod_{k=1}^{j-1} r_{i\sigma_i(k)} \quad (j \ge 2)$$

(Eqs. (1)-(3) of the source). If all variables have $k$ states, the penalty of a parent set depends only on its size $s$: $u(s) = \sum_{j=1}^{s} \chi_{\alpha, (k-1)^2 k^{j-1}}$ (Proposition 3 of the source).

## Expansion

The first term is the log-likelihood in information form: maximizing $\sum_i 2N\, I(X_i, Pa_i)$ is maximum likelihood, which always prefers the complete network because mutual information never decreases when a parent is added. The penalty uses Kullback's result that, if $X_i$ and $X_j$ are conditionally independent given $Pa_i$, then $2N\, I(X_i, X_j \mid Pa_i)$ is approximately $\chi^2$ with $(r_i - 1)(r_j - 1) q_i$ degrees of freedom, $q_i$ being the number of joint states of $Pa_i$; adding parents one at a time telescopes these tests. A parent therefore raises the score only if its conditional information with the child exceeds the level-$\alpha$ critical value. Because the score decomposes over nodes and inter-slice edges cannot create cycles, each node's parent set can be optimized separately, which is exploited by exact parent-set search.

## Sources

- N. X. Vinh, M. Chetty, R. Coppel and P. P. Wangikar, *Gene regulatory network modeling via global optimization of high-order dynamic Bayesian network*, BMC Bioinformatics 13 (2012), 131. DOI: <https://doi.org/10.1186/1471-2105-13-131>. PMCID: PMC3433362.
