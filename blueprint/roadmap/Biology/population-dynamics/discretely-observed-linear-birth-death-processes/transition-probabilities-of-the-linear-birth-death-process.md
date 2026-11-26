# Transition probabilities of the linear birth-death process and the Galton-Watson estimator

Let $X(t)$ be a linear birth-death process with constant per-capita birth rate $\lambda > 0$ and death rate $\mu \ge 0$, $\lambda \neq \mu$: in a time element $dt$ the population moves from $n$ to $n+1$ with probability $\lambda n\, dt + o(dt)$ and to $n-1$ with probability $\mu n\, dt + o(dt)$. Write $\alpha = \lambda - \mu$ (Malthusian parameter) and

$$ A(t) = \frac{\mu\,(e^{\alpha t} - 1)}{\lambda e^{\alpha t} - \mu}, \qquad B(t) = \frac{\lambda}{\mu} A(t) = \frac{\lambda\,(e^{\alpha t} - 1)}{\lambda e^{\alpha t} - \mu}. $$

**Transition probabilities.** For $n \ge 1$, $m \ge 1$ and $P_{nm}(t) = \Pr[X(s+t) = m \mid X(s) = n]$,

$$ P_{nm}(t) = \sum_{j=1}^{\min(n,m)} \binom{m-1}{j-1} \binom{n}{j} A(t)^{n-j} B(t)^{m-j} \bigl[1 - A(t)\bigr]^j \bigl[1 - B(t)\bigr]^j, $$

which is equivalent to Keiding's form $P_{nm}(t) = \sum_{j=0}^{\min(m,n)} \binom{n}{j} \binom{n+m-j-1}{n-1} A^{n-j} B^{m-j} (1 - A - B)^j$, and can also be written as $P_{nm}(t) = A^n B^m \binom{n+m-1}{m}\, {}_2F_1\!\left(-m, -n; 1-n-m; \tfrac{1}{A} + \tfrac{1}{B} - 1\right)$.

**Galton-Watson estimator.** If the process is observed at equidistant times $0, \tau, 2\tau, \dots, k\tau$, the skeleton $X(j\tau)$ is a linear-fractional Galton-Watson process, and the maximum likelihood estimator of $\alpha$ is

$$ \widehat\alpha = \frac{1}{\tau} \log \frac{X(\tau) + X(2\tau) + \dots + X(k\tau)}{X(0) + X(\tau) + \dots + X((k-1)\tau)}. $$

## Expansion

Each of the $n$ initial individuals independently either has no descendants at time $t$, with probability $A(t)$, or survives, and conditionally on survival its progeny size is geometric on $\{1, 2, \dots\}$ with success probability $1 - B(t)$. Choosing which $j$ ancestors survive gives $\binom{n}{j} A^{n-j} (1-A)^j$, and the total progeny of $j$ survivors is a sum of $j$ independent geometric variables, a negative binomial with probability $\binom{m-1}{j-1} (1-B)^j B^{m-j}$ of equaling $m$; summing over $j$ gives the formula. At equidistant times $A$ and $B$ are constants, the likelihood depends on $\alpha$ through the offspring mean $e^{\alpha\tau}$ of the embedded Galton-Watson process, and the classical ratio estimator of that mean (total offspring over total parents) gives $\widehat\alpha$.

## Sources

- Xiaochen Long, Marek Kimmel, "An Approximate Maximum Likelihood Estimator for Discretely Observed Linear Birth-and-Death Processes", arXiv (2025). Section 3.1 and its appendix derivation. <https://doi.org/10.48550/arXiv.2508.07527>
- N. Keiding, "Maximum likelihood estimation in the birth-and-death process", Annals of Statistics 3 (1975), 363-372.
