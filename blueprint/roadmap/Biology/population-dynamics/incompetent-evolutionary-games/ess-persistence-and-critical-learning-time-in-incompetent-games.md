# ESS persistence and critical learning time in incompetent games

**Model.** In a one-population matrix game with fitness matrix $R\in\mathbb R^{n\times n}$, players may fail to execute the strategy they choose: $q_{ij}$ is the probability that choosing $i$ results in executing $j$, collected in a stochastic matrix $Q$. The *incompetent* fitness matrix is $R^Q=QRQ^{\mathsf T}$. Learning moves $Q$ from a starting incompetence matrix $S$ to the identity,

$$Q(\lambda)=(1-\lambda)S+\lambda I,\qquad \lambda\in[0,1],$$

e.g. along the sigmoid $\lambda(t)=\big(1+e^{-a(\alpha t-b)}\big)^{-1}$. Strategy frequencies $x$ follow the replicator dynamics $\dot x_i=x_i\big(e_i^{\mathsf T}R(\lambda)x-x^{\mathsf T}R(\lambda)x\big)$ with $R(\lambda)=R^{Q(\lambda)}$. Write $\Gamma_\lambda$ for the game with fixed $\lambda$; a *critical value* $\lambda^c$ is a bifurcation value of its replicator dynamics.

**Theorem (persistence near full competence).** Let $\tilde x$ be an ESS of the fully competent game $\Gamma_1$ and $\lambda^u$ the largest critical value. If $\|Q(\lambda)-I\|$ is sufficiently small for $\lambda\in(\lambda^u,1]$, then $\Gamma_\lambda$ has an ESS $\tilde x(\lambda)$ with $\tilde x(\lambda)\to\tilde x$ as $\lambda\to1^-$.

**Theorem (critical learning time).** Under the sigmoid learning law, with $\lambda^u$ exceeding all bifurcation values, $\tilde x$ becomes an ESS of $\Gamma_{\lambda(t)}$ on some interval $(t,\infty)$ with $t>t^u$, where $\lambda(t^u)=\lambda^u$, i.e.

$$t^u=\frac1\alpha\Big(b-\frac1a\ln\frac{1-\lambda^u}{\lambda^u}\Big).$$

**Theorem (uniform starting incompetence).** If $s_{ij}=1/n$ for all $i,j$, then $\Gamma_\lambda$ is equivalent (same ESSs, rest points and stability) to the game with $\hat R(\lambda)=R+\frac{1-\lambda}{\lambda n}RJ$, $J$ the all-ones matrix, and $\det\hat R(\lambda)=\lambda^{-1}\det R$. If $\tilde x$ is an interior ESS of $\Gamma_1$, then for $\mu=1-\lambda$ sufficiently close to $0$,

$$\tilde x(\mu)=\frac1{1-\mu}\Big(\tilde x-\frac\mu n\mathbf 1\Big)$$

is an interior ESS of the incompetent game; if moreover $R$ has constant row sums, $\tilde x$ itself is an interior ESS for every $\lambda\in[0,1]$.

**Theorem (periodic environments).** If $\lambda(t)$ is periodic with period $2\pi/\alpha$ and $\|S-I\|$ is small, the replicator trajectory converging to an ESS of $\Gamma_1$ is shadowed by a periodic solution of the forced system.

## Expansion

Near an ESS, $V(x)=\prod_ix_i^{\tilde x_i}$ is a strict local Lyapunov function with $\dot V=V(\tilde x^{\mathsf T}Rx-x^{\mathsf T}Rx)>0$; a small perturbation of $R$ preserves this strictness, giving persistence. Before $t^u$ the incompetent game can sit beyond a bifurcation, so the population may temporarily approach another state; the critical time quantifies how slow learning (small $a$ or $\alpha$, large $b$) delays convergence. Adding column-constant matrices and positive rescaling leave replicator dynamics unchanged (Bomze), which reduces uniform incompetence to the rank-one perturbation $RJ$. Differences in starting incompetence and learning speed between competing types (*learning advantages*) can open an evolutionarily weak phase in which even an ESS population is vulnerable to invasion.

## Depends on

- [Replicator dynamics](../replicator-dynamics/is-solution.md)

## Sources

- Maria Kleshnina, Jerzy A. Filar, Cecilia Gonzalez Tokman, "Nonlinear learning and learning advantages in evolutionary games", arXiv:1810.09852: Section 2 (model), Theorem 3.1, Lemma 3.2, Theorem 3.3 and Corollary 1 (critical time), Theorem 4.2 (periodic forcing), Lemmas 5.1–5.3, 5.5 and Theorem 5.6 (uniform incompetence). <https://doi.org/10.48550/arXiv.1810.09852>
