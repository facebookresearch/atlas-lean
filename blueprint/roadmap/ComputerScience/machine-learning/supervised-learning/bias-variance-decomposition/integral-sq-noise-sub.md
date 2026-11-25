# The bias-variance decomposition

Let $(\Omega, \mu)$ be a probability space, with
expectation $\mathbb{E}$ and variance $\operatorname{Var}$ taken with respect to $\mu$. Let $f$ be
a real number, and let $\varepsilon$ (the noise) and $\hat Y$ (the predictor) be square-integrable
real random variables on $\Omega$ such that $\mathbb{E}[\varepsilon] = 0$ and $\varepsilon$ is
independent of $\hat Y$. Then the expected squared error of $\hat Y$ for the response
$\varepsilon + f$ is the noise variance plus the squared bias plus the variance of the predictor:
$\mathbb{E}[(\varepsilon + f - \hat Y)^2] = \operatorname{Var}(\varepsilon) +
(f - \mathbb{E}[\hat Y])^2 + \operatorname{Var}(\hat Y)$.
