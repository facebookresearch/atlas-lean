# Transition probabilities of the linear birth-death process and the Galton-Watson estimator

Let $X(t)$ be a linear birth-death process with constant per-capita birth rate $\lambda > 0$ and death rate $\mu > 0$, $\lambda \neq \mu$: in a time element $dt$ the population moves from $n$ to $n+1$ with probability $\lambda n\, dt + o(dt)$ and to $n-1$ with probability $\mu n\, dt + o(dt)$. Write $\alpha = \lambda - \mu$ (Malthusian parameter) and

$$ A(t) = \frac{\mu\,(e^{\alpha t} - 1)}{\lambda e^{\alpha t} - \mu}, \qquad B(t) = \frac{\lambda}{\mu} A(t) = \frac{\lambda\,(e^{\alpha t} - 1)}{\lambda e^{\alpha t} - \mu}. $$

**Transition probabilities.** For $n \ge 1$, $m \ge 1$ and $P_{nm}(t) = \Pr[X(s+t) = m \mid X(s) = n]$,

$$ P_{nm}(t) = \sum_{j=0}^{\min(m,n)} \binom{n}{j} \binom{n+m-j-1}{n-1} A(t)^{n-j} B(t)^{m-j} \bigl[1 - A(t) - B(t)\bigr]^j, $$

equivalently $P_{nm}(t) = \sum_{j=1}^{\min(n,m)} \binom{m-1}{j-1} \binom{n}{j} A(t)^{n-j} B(t)^{m-j} \bigl[1 - A(t)\bigr]^j \bigl[1 - B(t)\bigr]^j$, and $P_{n0}(t) = A(t)^n$.

**Galton-Watson estimator.** If the process is observed at equidistant times $0, \tau, 2\tau, \dots, k\tau$, the skeleton $X(j\tau)$ is a linear-fractional Galton-Watson process, and the maximum likelihood estimator of $\alpha$ is

$$ \widehat\alpha = \frac{1}{\tau} \log \frac{X(\tau) + X(2\tau) + \dots + X(k\tau)}{X(0) + X(\tau) + \dots + X((k-1)\tau)}. $$

## Expansion

Each of the $n$ initial individuals independently either has no descendants at time $t$, with probability $A(t)$, or survives, and conditionally on survival its progeny size is geometric on $\{1, 2, \dots\}$ with success probability $1 - B(t)$. Choosing which $j$ ancestors survive gives $\binom{n}{j} A^{n-j} (1-A)^j$, and the total progeny of $j$ survivors is a sum of $j$ independent geometric variables, a negative binomial with probability $\binom{m-1}{j-1} (1-B)^j B^{m-j}$ of equaling $m$; summing over $j$ gives the second form. At equidistant times $A$ and $B$ are constants, the likelihood depends on $\alpha$ through the offspring mean $e^{\alpha\tau}$ of the embedded Galton-Watson process, and the classical ratio estimator of that mean (total offspring over total parents) gives $\widehat\alpha$.

## Sources

- Niels Keiding, "Maximum likelihood estimation in the birth-and-death process", Annals of Statistics 3 (1975), 363–372, <https://doi.org/10.1214/aos/1176343062>. The maximum likelihood estimator for observation at equidistant times.
- Simon Tavaré, "The linear birth‒death process: an inferential retrospective", Advances in Applied Probability 50A (2018), 253–269, <https://doi.org/10.1017/apr.2018.84>. Eqs (9), (11) and (12): the transition probabilities $P_{nm}(t)$ in both forms and $P_{n0}(t)$.
