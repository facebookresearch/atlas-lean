# Mean squared error

Let $\mu$ be a probability measure on a measurable space $S$, let
$W : S \to \mathbb{R}$ be an estimator and $\theta \in \mathbb{R}$ a target value, and suppose the
squared error $x \mapsto (W(x) - \theta)^2$ is $\mu$-integrable. The mean squared error of $W$ at
$\theta$ under $\mu$ is the real number $\int_S (W(x) - \theta)^2 \, d\mu(x)$.

The integrability hypothesis is part of the definition: without it no finite mean squared error is
defined.

## Sources

- Casella–Berger, Definition 7.3.1; blueprint `af_fd40353442120bd19166139d`.
