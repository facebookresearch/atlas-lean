# The Wald estimand depends only on the observed law

A binary-instrument potential-outcomes model on a measurable space $\Omega$ consists of a measurable instrument $Z : \Omega \to \{0,1\}$, measurable potential treatments $D(z) : \Omega \to \{0,1\}$ and measurable potential outcomes $Y(z,d) : \Omega \to \mathbb R$ for $z, d \in \{0,1\}$; the observed treatment is $D = D(Z)$ and the observed outcome is $Y = Y(Z, D(Z))$. For a measure $\mu$ on $\Omega$, the Wald estimand is

$$W(\mu) = \frac{\mathbb E_\mu[Y \mid Z = 1] - \mathbb E_\mu[Y \mid Z = 0]}{\mathbb E_\mu[D \mid Z = 1] - \mathbb E_\mu[D \mid Z = 0]},$$

where $\mathbb E_\mu[\,\cdot \mid Z = z]$ is the integral against the conditional measure $\mu[\,\cdot \mid Z = z]$ (the zero measure, so the conditional expectation is $0$, when $\mu(Z = z)$ is $0$ or infinite), and $x / 0 = 0$.

Let two such models be given on $(\Omega, \mu)$ and $(\Omega', \mu')$, with arbitrary measures $\mu, \mu'$. If the observed triples $(Z, D, Y)$ and $(Z', D', Y')$ have the same law, then $W(\mu) = W'(\mu')$: the Wald estimand depends only on the joint law of the observed $(Z, D, Y)$ (the observed-law half of Imbens & Angrist 1994, Theorem 1).
