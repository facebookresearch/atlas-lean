# The complete-case mean as an integral against the conditional measure

Let $\mu$ be a measure on a measurable space $\Omega$, $R \subseteq \Omega$ measurable and $Y : \Omega \to \mathbb R$. Then the complete-case mean is the integral of $Y$ against the conditional measure given response:

$$\frac{\int \mathbf 1_R\, Y \, d\mu}{\mu(R)} = \int Y \, d\mu[\,\cdot \mid R],$$

where $\mu[\,\cdot \mid R] = \mu(R)^{-1}\, \mu|_R$ with $\infty^{-1} = 0$ and $0^{-1} = \infty$, so it is the zero measure when $\mu(R)$ is $0$ or infinite; on the left $\mu(R)$ is read as a real number, $0$ when infinite. Both sides are $0$ when $\mu(R)$ is $0$ or infinite, and integrals of non-integrable functions are $0$. Only for $0 < \mu(R) < \infty$ is $\mu[\,\cdot \mid R]$ a probability measure, the conditional law given response.
