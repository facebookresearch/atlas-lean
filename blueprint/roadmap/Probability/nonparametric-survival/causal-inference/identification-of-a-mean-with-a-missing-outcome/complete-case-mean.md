# Complete-case mean

Let $\mu$ be a measure on a measurable space $\Omega$, $R \subseteq \Omega$ the response event and $Y : \Omega \to \mathbb R$ an outcome observed only on $R$. The complete-case mean is the average of $Y$ over the respondents,

$$\bar Y_{cc} = \frac{\int \mathbf 1_R\, Y \, d\mu}{\mu(R)},$$

with $x / 0 = 0$. Here $\mu(R)$ is read as a real number, $0$ when $\mu(R) = \infty$, and the integral is a Bochner integral, $0$ when $\mathbf 1_R Y$ is not integrable; so the value is $0$ when $\mu(R)$ is $0$ or infinite. It depends on $Y$ only through its values on $R$, so it is an observed-data estimand.
