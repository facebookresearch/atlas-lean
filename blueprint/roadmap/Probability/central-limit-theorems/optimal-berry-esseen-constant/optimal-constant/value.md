# The optimal Berry–Esseen constant

Call a real number $C$ admissible if for every
probability measure $\mu$ on $\mathbb{R}$ with mean $0$, variance $1$ and finite third absolute
moment $\rho = \int |x|^3 \, d\mu$, and every positive integer $n$,

$$\sup_{x \in \mathbb{R}} |F_n(x) - \Phi(x)| \le \frac{C \rho}{\sqrt{n}},$$

where $F_n$ is the distribution function of $(X_1 + \dots + X_n)/\sqrt{n}$ for independent
random variables $X_1, X_2, \dots$ with law $\mu$, and $\Phi$ is the standard normal
distribution function. The optimal Berry–Esseen constant is the infimum of the admissible $C$.

The set of admissible constants is nonempty (it contains $42$) and bounded below by $0$, so
this is a genuine real infimum.
