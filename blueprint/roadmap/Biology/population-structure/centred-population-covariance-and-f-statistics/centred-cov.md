# Centred leaf covariance

Let $\mu$ be a measure on a measurable space $\Omega$ and $P$ a finite set of populations with allele frequencies $p_X : \Omega \to \mathbb{R}$. The centred leaf covariance is

$$K(X, Y) = \int (p_X - \bar p)(p_Y - \bar p) \, d\mu, \qquad X, Y \in P,$$

where $\bar p$ is the [mean frequency across populations](pop-mean.md), with the convention that the integral of a non-integrable function is $0$. The frequencies are centred across populations at each outcome, not over $\Omega$, so $K$ is not a covariance over $\Omega$.
