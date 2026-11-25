# Unbiased f2 estimator

For natural numbers $m_A, m_B$ and real numbers $x_A, x_B$, put (Patterson et al. 2012, Appendix)

$$\hat f_2 = \Bigl(\frac{x_A}{m_A} - \frac{x_B}{m_B}\Bigr)^2 - \frac{\hat h(m_A, x_A)}{m_A} - \frac{\hat h(m_B, x_B)}{m_B},$$

where $\hat h$ is the [heterozygosity estimator](het-hat.md), with the convention $a/0 = 0$.

For $m_A, m_B \ge 2$ and independent binomial counts $x_A \sim \mathrm{Bin}(m_A, q_A)$, $x_B \sim \mathrm{Bin}(m_B, q_B)$, it is an [unbiased estimator](integral-f2-hat.md) of $(q_A - q_B)^2$; its realized values may be negative.

## Sources

- N. Patterson, P. Moorjani, Y. Luo, S. Mallick, N. Rohland, Y. Zhan, T. Genschoreck, T. Webster, D. Reich, *Ancient admixture in human history*, Genetics 192 (2012), 1065–1093 (the D-statistic; Appendix: unbiased f-statistic estimators).
