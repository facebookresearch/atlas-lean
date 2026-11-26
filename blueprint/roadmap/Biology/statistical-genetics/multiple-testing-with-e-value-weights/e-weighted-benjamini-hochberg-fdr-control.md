# False discovery rate of the e-weighted Benjamini–Hochberg procedure

Let $P_1, \dots, P_K$ be p-values and $E_1, \dots, E_K$ e-values for hypotheses $H_1, \dots, H_K$, with null set $\mathcal{N}$ of size $K_0 = \pi_0 K$. The ep-BH procedure at level $\alpha$ applies the [Benjamini–Hochberg procedure](../../../Probability/hypothesis-testing/benjamini-hochberg-procedure/bh-rejections.md) to $P_k^* = Q(P_k, E_k) = (P_k / E_k) \wedge 1$; equivalently it is the weighted Benjamini–Hochberg procedure with p-values $P_k$ and unnormalized weights $E_k$.

**Theorem.** Suppose the vector $(P_k)_{k \le K}$ is independent of the vector $(E_k)_{k \le K}$, and $(P_k)$ is positively regression dependent on a subset (for each null $k$ and increasing set $A$, $x \mapsto \Pr\{(P_\ell) \in A \mid P_k \le x\}$ is increasing). Then the ep-BH procedure has false discovery rate at most $\pi_0 \alpha$. No assumption is made on the dependence among the e-values.

## Depends on

- [Benjamini–Hochberg rejection set](../../../Probability/hypothesis-testing/benjamini-hochberg-procedure/bh-rejections.md)
- [Quotient combiner of an independent p-value and e-value](quotient-combiner-of-independent-p-and-e-values.md)

## Expansion

Condition on the e-values: ep-BH becomes weighted BH with fixed weights $E_k$, and the weighted BH bound under positive regression dependence gives $\mathbb{E}[\mathrm{FDP} \mid (E_k)] \le \sum_{k \in \mathcal{N}} E_k \alpha / K$. Taking expectations and using $\mathbb{E}[E_k] \le 1$ for nulls yields $\mathrm{FDR} \le K_0 \alpha / K = \pi_0 \alpha$. Unlike normalized weighted BH, the weights need not average to one, so informative e-values can raise power without a renormalization penalty. The paper also shows that if each null pair $(P_k, E_k)$ is merely independent, any p-value procedure valid under arbitrary dependence stays valid when applied to the $P_k^*$.

## Sources

- N. Ignatiadis, R. Wang and A. Ramdas, *E-values as unnormalized weights in multiple testing*, Biometrika (2023). <https://doi.org/10.1093/biomet/asad057> Definitions 2.2, 2.4, 2.9 and 4.2, Assumption 4.6 and Theorem 4.7 (with Theorem 4.3).
