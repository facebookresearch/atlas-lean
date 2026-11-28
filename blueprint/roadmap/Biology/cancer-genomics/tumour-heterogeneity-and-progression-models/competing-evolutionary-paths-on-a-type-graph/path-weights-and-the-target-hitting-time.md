# Path weights and the target hitting time on a type graph

**Model.** Cell types are the vertices $\{1, \dots, N\}$ of a finite directed acyclic graph $G$. A type-$x$ cell divides at rate $\alpha(x)$, dies at rate $\beta(x)$, and produces a type-$y$ cell (by transition, e.g. mutation) at rate $\nu(x,y)$ for each edge $(x,y)$; cells act independently. Write $\lambda(x) = \alpha(x) - \beta(x)$ and $\alpha = \alpha(1)$, $\beta = \beta(1)$, $\lambda = \lambda(1)$. Assume the root is the fittest non-target type: $\lambda > 0$ and $\lambda(x) < \lambda$ for $2 \le x \le N-1$. Start with $z$ root cells and let $T = \inf\{t : Z_N(t) > 0\}$ be the time the target $N$ is first populated.

**Path weights.** For a root-to-target path $p = (p_1 = 1, p_2, \dots, p_{l+1} = N)$,

$$w(p) = \nu(p_1, p_2)\prod_{i=2}^{l}\frac{\nu(p_i, p_{i+1})}{\lambda - \lambda(p_i)}, \qquad \phi_N = \sum_{p} w(p),$$

transition rates along the path divided by fitness costs.

**Growth of intermediate types.** Almost surely $e^{-\lambda t}Z_x(t) \to W\,\Phi_x$ for $1 \le x \le N-1$, where $\Phi_1 = 1$, $\Phi_x = \phi_x/(\lambda - \lambda(x))$ with $\phi_x$ the total weight of paths from $1$ to $x$, and $W$ is a sum of $K$ i.i.d. exponential variables with rate $\lambda/\alpha$, $K \sim \mathrm{Binomial}(z, \lambda/\alpha)$.

**Theorem (hitting time).** As the target-seeding rates $\nu(x, N) \to 0$,

$$P(T - \mu > t) \to \left(\frac{\lambda/\alpha}{1 + e^{\lambda t}} + \frac{\beta}{\alpha}\right)^{z}, \qquad \mu = \frac{1}{\lambda}\log\frac{\lambda^2}{\alpha\,\phi_N} .$$

Hence $P(T < \infty) \approx 1 - (\beta/\alpha)^z$, the fluctuations of $T$ depend only on root parameters, and all other parameters enter through the centring $\mu$. For a path graph $1 \to 2 \to \dots \to N$ with $z = 1$ the median is approximately

$$t_{1/2} \approx \frac1\lambda\log\frac{\lambda^2}{\alpha\,\nu(1,2)} + \frac1\lambda\sum_{i=2}^{N-1}\log\frac{\lambda - \lambda(i)}{\nu(i, i+1)} .$$

For the first target cell whose lineage survives, replace $\nu(x, N)$ by $\nu(x,N)\lambda(N)/\alpha(N)$.

## Expansion

Each intermediate type is fed by its predecessors and grows at its own slower rate, so in the long run it rides the root's exponential $e^{\lambda t}$ with amplitude $\Phi_x$; each edge contributes a factor $\nu/(\lambda - \lambda(x))$ from integrating $\nu e^{\lambda s}$ against $e^{\lambda(x)(t-s)}$. Target cells then arrive as a Poisson process of rate $\sum_x \nu(x,N)Z_x(t) \approx \phi_N W e^{\lambda t}$, so $P(T > t \mid W) \approx \exp(-\phi_N W e^{\lambda t}/\lambda)$; averaging over the binomial–Erlang law of $W$ gives the stated limit. The single root-level random variable $W$ is why the shape of the law is universal.

## Sources

- M. D. Nicholson, T. Antal, "Competing evolutionary paths in growing populations with applications to multidrug resistance", PLoS Computational Biology 15(4) (2019) e1006866, General framework (equations (1)–(3)), Theorem 1 with equations (4)–(9), and Materials and methods, Theorem 3, <https://doi.org/10.1371/journal.pcbi.1006866>, PMCID: PMC6483269.
