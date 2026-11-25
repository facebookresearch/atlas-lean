# Negative binomial mass function with size and mean

For real $\theta, \mu$ and $k \in \mathbb{N}$, the negative binomial mass function with size $\theta$ and
mean $\mu$ is

$$\mathrm{NB}(k; \theta, \mu) = \frac{\theta^{(k)}}{k!} \Bigl(\frac{\theta}{\theta + \mu}\Bigr)^\theta \Bigl(\frac{\mu}{\theta + \mu}\Bigr)^k,$$

with the rising factorial $\theta^{(k)} = \theta(\theta+1)\cdots(\theta+k-1) = \Gamma(\theta + k)/\Gamma(\theta)$
(for $\theta > 0$), the real power $(\theta/(\theta + \mu))^\theta$, and a quotient with zero
denominator read as $0$; here real powers: the usual power of a positive base, $0^0 = 1$ and $0^s = 0$ for $s \ne 0$, and $x^s = |x|^s \cos(\pi s)$ for $x < 0$. For $\theta > 0$ and $\mu \ge 0$ it is a probability mass function on
$\mathbb{N}$ with mean $\mu$, and for $\mu = 0$ the point mass at $0$. Outside that domain the formula
need not be a probability mass function, though it can be: for $\theta = \mu = 0$, with $0^0 = 1$ and
$0^{(k)} = 0$ for $k \ge 1$, it is again the point mass at $0$. For a negative base the power is not a
real root: for $\theta = \frac13$ and $\mu = -\frac23$, $\mathrm{NB}(0; \theta, \mu) = (-1)^{1/3} = \cos(\pi/3) = \frac12$.
