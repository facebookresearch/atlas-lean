# Energy-structured individual-based model and its generation process

**Individual dynamics.** A species is characterized by the energy $x_0 > 0$ given to each newborn, and the resource is held at a constant level $R \ge 0$. An individual's energy $\xi_t$ is a piecewise deterministic Markov process:

- between jumps, $\dot\xi_t = g(\xi_t, R) := \phi(R)\psi(\xi_t) - \ell(\xi_t)$, where $\ell$ (metabolic loss) and $\psi$ (resource conversion) are positive, increasing and continuous, $\phi$ is continuous, nondecreasing, $\phi(0) = 0$ and $\phi(R) \to 1$ as $R \to \infty$, and $g(\cdot, R)$ is $C^1$;
- *birth* at rate $b_{x_0}(\xi) = \mathbb 1_{\xi > x_0}\tilde b(\xi)$, after which $\xi \mapsto \xi - x_0$ and an offspring starts at energy $x_0$;
- *death* at rate $d(\xi)$, with $\tilde b, d$ positive and continuous.

A path is *biologically relevant* if death occurs before the energy reaches $0$ or $+\infty$, that is, $T_d < \infty$. Let

$$K_{x_0,R}f(\xi_0) = \int_0^{t_{\max}(\xi_0,R)} b_{x_0}(A_{\xi_0,R}(u))\,e^{-\int_0^u (b_{x_0}+d)(A_{\xi_0,R}(\tau))\,d\tau} f\big(A_{\xi_0,R}(u) - x_0\big)\,du,$$

where $A_{\xi_0,R}$ is the deterministic flow; $K_{x_0,R}\mathbf 1(\xi_0)$ is the probability that the next jump is a birth.

- **Assumption 1** (energy avoids $0$): $\int_0^{x_0} \frac{d}{\ell}(x)\,dx = +\infty$ for all $x_0 > 0$.
- **Assumption 2** (energy avoids $+\infty$): whenever $g(\cdot, R) > 0$ on $[\xi_0, \infty)$, $K^k_{x_0,R}\mathbf 1(\xi_0) \to 0$ as $k \to \infty$ and $\int_{\xi_0}^\infty \frac{b_{x_0}+d}{g(x,R)}\,dx = +\infty$.

**Theorem (relevance criterion).** Assumptions 1 and 2 hold if and only if $\mathbb P_{x_0,R,\xi_0}(T_d < \infty) = 1$ for all $x_0, \xi_0 > 0$ and $R \ge 0$. Under them the individual process is a PDMP with an explicit extended generator.

**Generation process.** Let $\Upsilon_n$ be the number of individuals of generation $n$ in the population built from independent individual paths, and let $N_{x_0,R,\xi_0}$ be the lifetime number of offspring, with mean $m_{x_0,R}(\xi_0)$. If $N_{x_0,R,\xi_0} < \infty$ almost surely (implied by Assumption 2), then $(\Upsilon_n)_{n \ge 1}$ is a Galton-Watson process with offspring law that of $N_{x_0,R,x_0}$. Consequently, under Assumptions 1 and 2, *supercriticality* (Assumption 3: for each $x_0$ and all large $R$, the population survives forever with positive probability) is equivalent to: for every $x_0 > 0$ there is $R_0$ with $m_{x_0,R}(x_0) > 1$ for all $R > R_0$. Assumptions 1 to 3 imply that for every $x_0$ some resource level gives $g(x_0, R) > 0$.

## Expansion

Assumption 1 forces death before starvation: near zero energy the death hazard accumulated along the decreasing flow diverges. Assumption 2 handles unbounded growth: either infinitely many births or an infinite hazard integral stop the energy from escaping to infinity in finite time without death. Because the resource is fixed, individuals do not interact, which gives the branching property and makes the generation sizes a Galton-Watson process; supercriticality reduces to a mean-offspring condition for a newborn.

## Sources

- S. Billiard, V. Brodu, N. Champagnat and C. Fritsch, "An individual-based stochastic model reveals strong constraints on allometric relationships with minimal metabolic and ecological assumptions", arXiv preprint (2025), Assumptions 1 to 5, Theorem 1, Propositions 1 to 3 and Lemma 4. <https://doi.org/10.48550/arXiv.2501.12257>