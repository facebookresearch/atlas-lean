# Hudson's $F_{ST}$ as a ratio of expected sums

Under the hypotheses of the [unbiasedness of the summed f2 estimator](integral-sum-f2-hat.md) (in particular $m_{A,i}, m_{B,i} \ge 2$; Bhatia et al. 2013),

$$\frac{\int \sum_{i \in s} \hat f_2(m_{A,i}, m_{B,i}, X_{A,i}, X_{B,i}) \, d\mu}{\int \sum_{i \in s} \hat D(m_{A,i}, m_{B,i}, X_{A,i}, X_{B,i}) \, d\mu} = F_{ST}(q_A, q_B),$$

where $\hat f_2$ is the [f2 estimator](f2-hat.md), $\hat D$ the [denominator estimator](hudson-den-hat.md), $F_{ST}$ [Hudson's $F_{ST}$](hudson-fst.md) over the sites $s$, and $x/0 = 0$. This concerns the ratio of expectations; the expectation of the ratio of the estimated sums is in general different.
