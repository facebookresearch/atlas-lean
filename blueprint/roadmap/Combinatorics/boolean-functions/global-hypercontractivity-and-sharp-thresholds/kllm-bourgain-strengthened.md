# Bourgain's sharp-threshold theorem with global hypercontractivity

For every $K, \alpha > 0$ there are $r = r(K, \alpha)$ and $\eta = \eta(K, \alpha) > 0$ such that the following holds for every $0 < p \le 1/2$ and every monotone $\mathcal{A} \subseteq \{0,1\}^n$ with $\mu_p(\mathcal{A}) \in [\alpha, 1 - \alpha]$: if the total influence satisfies $p\, I_p[\mathcal{A}] \le K$, then there is $S \subseteq [n]$ with $|S| \le r$ such that

$$
\mu_p\bigl(\mathcal{A}_{S \to \mathbf{1}}\bigr) \ge \mu_p(\mathcal{A}) + \eta.
$$

## Proof sketch

If no small set boosts $\mathcal{A}$, its indicator is global; the level-$1$ global inequality then bounds the total influence from below, since $p\, I_p[\mathcal{A}]$ is proportional to the level-$1$ weight plus the higher-level weight, which the global level-$d$ inequality controls, contradicting $p\, I_p[\mathcal{A}] \le K$.

## Depends on

- [Global functions on the p-biased cube](pbiased-global-function.md)

## Proof depends on

- [Level-d inequality for global sets of small measure](kllm-level-d-global.md)
- [Sharp threshold from influences](../../../Probability/percolation/phase-transition/sharp-thresholds-from-influences/sth-sharp-threshold.md)
- [KKL inequality for $p$-biased measures](../kahn-kalai-linial-inequality/kkl-pbiased.md)

## Sources

- J. Bourgain, "On sharp thresholds of monotone properties" (appendix to E. Friedgut, "Sharp thresholds of graph properties, and the k-sat problem"), Journal of the American Mathematical Society 12 (1999) 1017-1054.
- P. Keevash, N. Lifshitz, E. Long, D. Minzer, "Hypercontractivity for global functions and sharp thresholds", Journal of the American Mathematical Society 37 (2024), arXiv:1906.05568.
