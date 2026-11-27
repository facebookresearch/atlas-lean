# Number of old families in the last coalescence of a stationary CB population

Work in the setting of [TMRCA and the bottleneck at the MRCA of a stationary CB population](tmrca-and-bottleneck-at-the-mrca-of-a-stationary-cb-population.md): a sub-critical branching mechanism $\psi$ satisfying (A1) and (A2), the functions $u(\lambda,t)$ and $c(t)$, $\tilde\psi'(\lambda) = \psi'(\lambda) - \psi'(0)$, the stationary CB with immigration $Z$, and its TMRCA $A$ at time $0$.

Let $N^A \ge 1$ be the number of **old families**: the number of families within the oldest clan alive at time $0$, excluding the immortal ancestral lineage that founds the immigration. Then $N^A + 1$ is the number of individuals involved in the last coalescent event of the genealogy of the time-$0$ population.

**Theorem.** For $a\in[0,1]$ and $t \ge 0$,

$$\mathbb E\big[a^{N^A}\mid A = t\big] = \frac{\psi'(c(t)) - \psi'((1-a)c(t))}{\tilde\psi'(c(t))} = 1 - \frac{\tilde\psi'((1-a)c(t))}{\tilde\psi'(c(t))},$$

so for every integer $n \ge 1$

$$\mathbb P(N^A = n\mid A = t) = (-1)^{n+1}\,\frac{c(t)^n\,\psi^{(n+1)}(c(t))}{n!\,\tilde\psi'(c(t))}.$$

If $\psi''(0+) < \infty$ (equivalently $\mathbb E[Z] < \infty$), then $\mathbb E[N^A\mid A = t] = \psi''(0)\,c(t)/\tilde\psi'(c(t))$, and $t\mapsto \mathbb E[N^A\mid A=t]$ is non-increasing, with $\mathbb P(N^A = 1\mid A=t) \to 1$ as $t\to\infty$: a deep last coalescence is likely binary.

For stable mechanisms $\psi(\lambda) = \alpha\lambda + c_0\lambda^{1+\alpha_0}$ with $c_0 > 0$, $\alpha_0\in(0,1]$, $\mathbb E[a^{N^A}\mid A=t] = 1 - (1-a)^{\alpha_0}$, so $N^A$ is independent of $A$; for $\alpha_0 = 1$ (quadratic branching) $N^A = 1$ a.s., and for $\alpha_0 \in (0,1)$, $\mathbb P(N^A = n) = \frac{\alpha_0}{n!}\prod_{k=1}^{n-1}(k - \alpha_0)$, a heavy-tailed law with $\psi''(0+) = \infty$.

## Depends on

- [TMRCA and the bottleneck at the MRCA of a stationary CB population](tmrca-and-bottleneck-at-the-mrca-of-a-stationary-cb-population.md)

## Expansion

Conditionally on $A = t$, the oldest surviving clan at time $-A$ is founded by a jump (or the quadratic branching part) of the immigration measure, whose descendants surviving time $t$ form a Poisson number of independent surviving sub-families with parameter proportional to $c(t)$ times the jump size. Thinning each survivor with probability $1-a$ replaces $c(t)$ by $(1-a)c(t)$ in $\tilde\psi'$; dividing by the total intensity $\tilde\psi'(c(t))$ gives the generating function. Expanding $\psi'((1-a)c(t))$ in powers of $a$ about $c(t)$ gives the point probabilities, and differentiating at $a = 1$ gives the mean. The monotonicity in $t$ is obtained in the source from the convexity of $\psi$, since $c(t)$ decreases in $t$.

## Sources

- Yu-Ting Chen, Jean-François Delmas, "Smaller population size at the MRCA time for stationary branching processes", *The Annals of Probability* 40 (2012), 2034–2068, <https://doi.org/10.1214/11-AOP668>; preprint arXiv:1009.0814, <https://doi.org/10.48550/arXiv.1009.0814>. Numbering of the arXiv version: Section 5, Definition 5.1, Proposition 5.2, Corollary 5.3, and the remarks following it.
