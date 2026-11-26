# Complete Case Mean

Let $\mu$ be a measure on a measurable space $\Omega$, $R \subseteq \Omega$ the response event and $Y : \Omega \to \mathbb R$ an outcome observed only on $R$. The complete-case mean is the average of $Y$ over the respondents,

$$\bar Y_{cc} = \frac{\int \mathbf 1_R\, Y \, d\mu}{\mu(R)},$$

with the value $0$ when $\mu(R) = 0$ (and $0$ for the integral when $\mathbf 1_R Y$ is not integrable). It depends on $Y$ only through its values on $R$, so it is an observed-data estimand.
