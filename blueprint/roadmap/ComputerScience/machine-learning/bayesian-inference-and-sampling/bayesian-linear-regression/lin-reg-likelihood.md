# The likelihood of Bayesian linear regression

**The likelihood of Bayesian linear regression** with one feature and known noise variance
$\sigma^2 \ge 0$, for fixed inputs $x \in \mathbb{R}^n$: the kernel from the weight
$w \in \mathbb{R}$ to the responses in $\mathbb{R}^n$ under which, given $w$, the responses are
independent with $y_i \sim \mathcal{N}(w x_i, \sigma^2)$. For $\sigma^2 \ne 0$ it is given by the
density $\prod_i \varphi(y_i; w x_i, \sigma^2)$ with respect to Lebesgue measure, where
$\varphi(t; \mu, \tau)$ is the Gaussian density with mean $\mu$ and variance $\tau$ at $t$; for
$\sigma^2 = 0$ it sends $w$ to the Dirac measure at $(w x_i)_i$.
