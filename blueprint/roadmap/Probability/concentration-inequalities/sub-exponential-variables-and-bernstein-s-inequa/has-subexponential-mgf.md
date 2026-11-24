# Sub-exponential random variable

A real random variable $X$ on a measure space $(\Omega, \mu)$ is *sub-exponential with parameters
$(\nu, \alpha)$*, for $\nu, \alpha \ge 0$, if for every $t$ with $\alpha |t| < 1$ the function
$e^{tX}$ is integrable and

$$\mathbb{E}[e^{tX}] \le e^{\nu^2 t^2 / 2}.$$

The condition concerns $X$ itself, not $X - \mathbb{E}[X]$; the source's notion,
about the mean, is the condition for $X - \mathbb{E}[X]$. With $\alpha = 0$ every $t$ is allowed
and the condition is the sub-Gaussian one with variance proxy $\nu^2$.

## Sources

- M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*, Cambridge University Press, 2019, §2.1.3 (sub-exponential variables).
- A. Rinaldo, *36-755 Advanced Statistics Theory I*, Lecture 3, Carnegie Mellon University, 2017: <https://www.stat.cmu.edu/~arinaldo/Teaching/36755/F17/Scribed_Lectures/F17_0911.pdf>, Definition 3.1.

## Background

- [Hoeffding's inequality](../hoeffding-s-inequality/README.md): the sub-Gaussian case $\alpha = 0$, where the bound holds for every $t$.
