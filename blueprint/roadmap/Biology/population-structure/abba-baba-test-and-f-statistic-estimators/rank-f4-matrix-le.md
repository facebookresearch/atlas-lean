# qpWave rank bound

Let $\mu$ be a measure and $p_X$ square-integrable allele frequencies of the populations $X$. Let $L_0, \dots, L_n$ and $R_0, \dots, R_r$ be populations, $S_0, \dots, S_k$ source populations and $a_{il}$ ($0 \le i \le n$, $0 \le l \le k$) real coefficients with $\sum_{l} a_{il} = 1$ for each $i$ (of any sign), such that (Reich et al. 2012; Patterson et al. 2012)

$$p_{L_i}(\omega) = \sum_{l=0}^{k} a_{il}\, p_{S_l}(\omega) \qquad \text{for all } i \text{ and } \omega.$$

Then the [qpWave matrix](f4-matrix.md) $\bigl(f_4(L_i, L_0; R_j, R_0)\bigr)_{1 \le i \le n,\, 1 \le j \le r}$ has rank at most $k$. The right populations are arbitrary.

## Sources

- D. Reich et al., *Reconstructing Native American population history*, Nature 488 (2012), 370–374.
- N. Patterson, P. Moorjani, Y. Luo, S. Mallick, N. Rohland, Y. Zhan, T. Genschoreck, T. Webster, D. Reich, *Ancient admixture in human history*, Genetics 192 (2012), 1065–1093 (the D-statistic; Appendix: unbiased f-statistic estimators).
