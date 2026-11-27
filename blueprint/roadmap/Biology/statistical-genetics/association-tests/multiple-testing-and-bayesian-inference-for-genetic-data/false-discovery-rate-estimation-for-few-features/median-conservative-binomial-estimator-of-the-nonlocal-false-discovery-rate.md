# Median-conservative binomial estimator of the nonlocal false discovery rate

**Setting.** Each of $N$ biological features (genes, proteins, metabolites) has a test statistic $T_i$ and an unknown indicator $A_i \in \{0,1\}$ of whether its null hypothesis is false, with $\pi_0 = \Pr(A_i = 0)$. For a rejection region $\mathcal{T}$ let $\Pi(\mathcal{T}) = \Pr(T_i \in \mathcal{T})$ and $\Pi_0(\mathcal{T}) = \Pr(T_i \in \mathcal{T} \mid A_i = 0)$, the latter known from the null distribution. The **nonlocal false discovery rate** is

$$\Phi(\mathcal{T}) = \Pr(A_i = 0 \mid T_i \in \mathcal{T}) = \frac{\pi_0\Pi_0(\mathcal{T})}{\Pi(\mathcal{T})} \le \frac{\Pi_0(\mathcal{T})}{\Pi(\mathcal{T})}.$$

Let $X = N_+(\mathcal{T})$ be the number of statistics in $\mathcal{T}$. Under independence $X \sim \operatorname{Binomial}(N, \Pi(\mathcal{T}))$, and the usual plug-in estimator $\widehat\Phi = \big(\Pi_0(\mathcal{T})/(X/N)\big)\wedge 1$ is the maximum-likelihood estimate of $\Pi_0/\Pi$ capped at $1$.

For $C\in[0,1]$ define the binomial significance function $S_C(\Pi; x) = \Pr(X > x; \Pi) + C\Pr(X = x; \Pi)$ and its inverse in $\Pi$, $S_C^{-1}(\cdot\,; x)$. The **confidence-posterior median** estimator is

$$\widetilde\Phi_C(\mathcal{T}; x) = \frac{\Pi_0(\mathcal{T})}{S_C^{-1}(1/2; x)}\wedge 1, \qquad \widetilde\Phi = \widetilde\Phi_1 .$$

**Proposition.** If $T_1,\dots,T_N$ are independent, then $\widetilde\Phi(\mathcal{T}; X)$ is median conservative: for every $\pi_0, \Pi_0(\mathcal{T}), \Pi(\mathcal{T}) \in [0,1]$,

$$\Pr\big(\widetilde\Phi(\mathcal{T}; X) \ge \Phi(\mathcal{T})\big) \ge \tfrac12 .$$

This holds for every $N$, including $N = 1$ or $2$, where the maximum-likelihood estimator $\widehat\Phi$ can fail median conservatism. If the $T_i$ are IID, then $\widehat\Phi$, every $\widetilde\Phi_C$ and the confidence-posterior means are all conservative as $N \to \infty$, meaning that $\Pr(\text{estimate} \ge \Phi) \to 1$.

## Depends on

- [Tail-area fdr is the posterior null probability given a region](../../../../../Probability/hypothesis-testing/two-groups-model-and-local-false-discovery-rates/cond-null-eq-tail-fdr.md)

## Expansion

The one-sided binomial bound $[S_1^{-1}(\alpha; X), 1]$ is a valid confidence interval for $\Pi(\mathcal{T})$, so $\Pr\big(S_1^{-1}(1/2; X) \le \Pi(\mathcal{T})\big) \ge 1/2$. On that event $\Pi_0/S_1^{-1}(1/2;X) \ge \Pi_0/\Pi \ge \Phi$, and capping at $1$ preserves the inequality because $\Phi \le 1$. The same construction applied to tail regions $[t_i,\infty)$ gives conservative predictors of the local false discovery rate built from as few as one or two p-values. Bickel derives these from nonlocal estimates through a monotone map whose conditional skewness is nonnegative (Theorem 3 and Corollary 4 of the source).

## Sources

- D. R. Bickel, "Simple estimators of false discovery rates given as few as one or two p-values without strong parametric assumptions", *Statistical Applications in Genetics and Molecular Biology* 12 (2013), 529–543, <https://doi.org/10.1515/sagmb-2013-0003>; preprint arXiv:1106.4490 (2011), Section 2, Proposition 1, Lemma 2, Theorem 3 and Corollary 4, <https://doi.org/10.48550/arXiv.1106.4490>.
