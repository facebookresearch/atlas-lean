# The Bregman divergence of the entropy is the Kullback–Leibler divergence

For $x$ in the [relative interior of the simplex](pos-simplex.md) and $u \in \mathbb{R}^n$ with $\sum_i u_i = 1$, the Bregman divergence of the [entropy](entropy.md) is

$$
V_x(u) = \sum_i u_i \log \frac{u_i}{x_i},
$$

with $0 \log 0 = 0$: the Kullback–Leibler divergence $\mathrm{KL}(u \,\|\, x)$ when $u$ is a probability vector.

## Sources

- A. Nemirovski, A. Juditsky, G. Lan and A. Shapiro, *Robust stochastic approximation approach to stochastic programming*, SIAM J. Optim. 19(4) (2009), 1574–1609; PDF at <https://people.eecs.berkeley.edu/~brecht/cs294docs/week1/09.Nemirovski.pdf>, Section 2.3, Example: the prox-function of the $\ell_1$-setup is $V(x, z) = \sum_i z_i \ln(z_i / x_i)$.
