# Integral cond selection Error eq

Let $(\Omega, \mu)$ be a probability space, $u : \Omega \to \mathbb R$ a measurable standard normal random variable and $c \in \mathbb R$. Then the mean of the selection error $u$ conditional on selection $\{-c \le u\}$ is the inverse Mills ratio (Heckman's second display, with unit selection variance):

$$\mathbb E_\mu[u \mid u \ge -c] = \lambda(c) = \frac{\varphi(c)}{\Phi(c)},$$

with $\varphi(x) = (2\pi)^{-1/2} e^{-x^2/2}$ the standard normal density and $\Phi$ the standard normal distribution function, the conditional expectation being the integral against $\mu$ conditioned on $\{-c \le u\}$.
