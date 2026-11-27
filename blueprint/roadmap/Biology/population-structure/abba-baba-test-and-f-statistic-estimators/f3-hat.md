# Unbiased f3 estimator

For natural numbers $m_C, m_A, m_B$ and real numbers $x_C, x_A, x_B$, put (Patterson et al. 2012, Appendix)

$$\hat f_3 = \Bigl(\frac{x_C}{m_C} - \frac{x_A}{m_A}\Bigr)\Bigl(\frac{x_C}{m_C} - \frac{x_B}{m_B}\Bigr) - \frac{\hat h(m_C, x_C)}{m_C},$$

where $\hat h$ is the [heterozygosity estimator](het-hat.md), with the convention $a/0 = 0$.

For $m_C \ge 2$, $m_A, m_B \ge 1$ and pairwise independent binomial counts $x_C \sim \mathrm{Bin}(m_C, q_C)$, $x_A \sim \mathrm{Bin}(m_A, q_A)$, $x_B \sim \mathrm{Bin}(m_B, q_B)$, it is an [unbiased estimator](integral-f3-hat.md) of $(q_C - q_A)(q_C - q_B)$; its realized values may be negative.

## Sources

- N. Patterson, P. Moorjani, Y. Luo, S. Mallick, N. Rohland, Y. Zhan, T. Genschoreck, T. Webster, D. Reich, *Ancient admixture in human history*, Genetics 192 (2012), 1065–1093 (the D-statistic; Appendix: unbiased f-statistic estimators).
