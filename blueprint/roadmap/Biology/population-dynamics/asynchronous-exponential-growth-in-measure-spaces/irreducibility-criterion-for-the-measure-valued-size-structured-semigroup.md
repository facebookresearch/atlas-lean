# Irreducibility criterion for the measure-valued size-structured semigroup

**Setting.** Consider the linear size-structured model on finite nonnegative Radon measures $\mu_t$ on $\mathbb{R}^+$,

$$\partial_t \mu_t + \partial_x\big(b(x)\mu_t\big) + c(x)\mu_t = \int_{\mathbb{R}^+} \eta(x) \, d\mu_t(x), \qquad b(0) D_\lambda \mu_t(0) = 0,$$

with growth rate $b > 0$, mortality $c$, and offspring-size distributions $\eta(x) \in \mathcal{M}^+(\mathbb{R}^+)$, under the regularity hypotheses ($b, c \in BL \cap C^1$, $x \mapsto \eta(x)$ bounded Lipschitz into measures with the flat norm) that make the model generate a positive strongly continuous semigroup $\mathcal{T}(t)$ on the flat-norm closure $E$ of the finite signed measures. The semigroup is *irreducible* if for every nonzero $\mu \in \mathcal{M}^+(\mathbb{R}^+)$ and every nonzero nonnegative bounded Lipschitz $\varphi$ there is $t > 0$ with $\int \varphi \, d(\mathcal{T}(t)\mu) > 0$.

**Proposition.** If there is $\hat y > 0$ such that

$$0 \in \bigcap_{y > \hat y} \operatorname{supp} \eta(y),$$

that is, every individual larger than $\hat y$ produces offspring arbitrarily close to size $0$, then $\mathcal{T}(t)$ is irreducible.

## Expansion

Because $b > 0$, any nonzero initial mass is transported to sizes above $\hat y$ in finite time, while mortality only multiplies mass by a positive factor. Individuals there place offspring mass in every neighbourhood of $0$, and transport from near $0$ then sweeps that mass across every interval $[0, x]$. Hence every nonnegative test function with nonzero support eventually sees positive mass. Irreducibility is the extra hypothesis that upgrades the finite-rank spectral decomposition of the semigroup to rank-one convergence, i.e. asynchronous exponential growth.

## Sources

- C. Düll, J. Z. Farkas, P. Gwiazda and A. Marciniak-Czochra, "Asynchronous exponential growth for structured population models in measure space", arXiv:2607.00658 (2026), Definition 3.6 and Proposition 4.5, <https://doi.org/10.48550/arXiv.2607.00658>.
