# The complete-case mean depends only on respondents

Let $\mu$ be a measure on a measurable space $\Omega$, $R \subseteq \Omega$ the response event and $Y : \Omega \to \mathbb R$ an outcome observed only on $R$. If $Y' : \Omega \to \mathbb R$ agrees with $Y$ on $R$, then the complete-case means agree:

$$\frac{\int \mathbf 1_R\, Y \, d\mu}{\mu(R)} = \frac{\int \mathbf 1_R\, Y' \, d\mu}{\mu(R)}$$

(with $x / 0 = 0$). Here $\mu(R)$ is read as a real number, $0$ when $\mu(R) = \infty$, and the integral is a Bochner integral, $0$ when $\mathbf 1_R Y$ is not integrable; so each side is $0$ when $\mu(R)$ is $0$ or infinite.
