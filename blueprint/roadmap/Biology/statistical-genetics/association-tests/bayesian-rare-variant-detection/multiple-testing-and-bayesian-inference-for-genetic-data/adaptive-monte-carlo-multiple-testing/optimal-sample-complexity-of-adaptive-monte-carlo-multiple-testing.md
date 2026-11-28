# Optimal sample complexity of adaptive Monte Carlo multiple testing

Work in the setting of [AMT recovering the full Monte Carlo BH discoveries](amt-recovers-full-monte-carlo-bh-discoveries.md): $m$ hypotheses, $n$ fMC samples per hypothesis, BH at level $\alpha$, and $N$ the total number of MC samples an algorithm draws. Call an algorithm *$\delta$-correct* if, conditionally on any set of fMC p-values, it outputs $\mathcal R^{\mathrm{fMC}}$ with probability at least $1-\delta$. The asymptotic regime is $m\to\infty$ with $n=\Omega(m)$.

**Upper bound.** Assume the ideal p-values are i.i.d. from an unknown distribution $F$ whose density $f$ is either constant ($f\equiv1$, all nulls) or continuous and monotonically decreasing (alternatives stochastically smaller than uniform). Running AMT with $\delta=\frac{1}{m\sqrt n}$ gives

$$
\mathbb E[N]=\tilde O(\sqrt n\,m),
$$

where $\tilde O$ hides logarithmic factors in $m$ and $n$; the full bound is $\tilde O(\sqrt n\,m\log\tfrac1\delta+\delta mn)$.

**Lower bound.** Assume the ideal p-values are i.i.d. from an unknown distribution with null proportion $\pi_0>0$. There is $\delta_0>0$ such that for every $\delta<\delta_0$, every $\delta$-correct algorithm satisfies

$$
\mathbb E[N]=\tilde\Omega(\sqrt n\,m).
$$

Hence AMT is optimal up to logarithmic factors, against the $nm$ samples of the full MC procedure.

## Expansion

The instance-wise bound (Theorem 2 of the source) charges hypothesis $p_{(i)}$ about $\min\{n,\ c\,p/\Delta_{(i)}^2\}$ samples, where $\Delta_{(i)}=|p_{(i)}-\tfrac{i\vee r^*}{m}\alpha|$ is its gap to the relevant BH line and $c=\Theta(\log(m/\delta))$: a binomial proportion near $p$ is resolved to accuracy $\Delta$ after about $p/\Delta^2$ draws. Under the density assumption the gaps of the $m$ ideal p-values to the limiting BH threshold are spread on a scale of $1/m$, and summing $\min\{n,1/\Delta^2\}$ over such gaps yields $\tilde O(\sqrt n\, m)$. For the lower bound, any correct algorithm must essentially exhaust the $n$ samples of each hypothesis whose fMC p-value lies within $c_1/\sqrt n$ above $\tau^*$ (Lemma 2 of the source); with $\pi_0>0$ there are on the order of $m/\sqrt n$ such hypotheses, costing $\Omega(\sqrt n\,m)$ samples. In a Parkinson's disease GWAS (448,001 SNPs) this cut running time from about two months to about an hour.

## Depends on

- [AMT recovers the full Monte Carlo BH discoveries](amt-recovers-full-monte-carlo-bh-discoveries.md)
- [Benjamini–Hochberg rejection set](../../../../../../Probability/hypothesis-testing/benjamini-hochberg-procedure/bh-rejections.md)

## Sources

- Martin J. Zhang, James Zou, David Tse. *Adaptive Monte Carlo Multiple Testing via Multi-Armed Bandits*, Proceedings of the 36th International Conference on Machine Learning, PMLR 97 (2019), 7512–7522, <https://proceedings.mlr.press/v97/zhang19t.html>; preprint arXiv:1902.00197, <https://doi.org/10.48550/arXiv.1902.00197>: Section 2 (problem formulation), Algorithm 1, Theorems 1–3, Proposition 1 and Remarks 1–2.
