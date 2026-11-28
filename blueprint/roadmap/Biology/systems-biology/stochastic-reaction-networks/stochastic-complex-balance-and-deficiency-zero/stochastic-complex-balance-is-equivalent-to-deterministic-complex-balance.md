# Stochastic complex balance is equivalent to deterministic complex balance

Let $\mathcal G = (\mathcal S, \mathcal C, \mathcal R)$ be a reaction network on species $S_1,\dots,S_n$, modelled stochastically as a continuous-time Markov chain on $\mathbb N^n$ that jumps from $x$ to $x + y' - y$ at rate $\lambda_{y\to y'}(x)$ for each reaction $y \to y'$; under mass action $\lambda_{y\to y'}(x) = \kappa_{y\to y'}\, x!/(x-y)!\,\mathbf 1_{\{x \ge y\}}$. A reaction is **active** on $x$ if $x \ge y$. For an irreducible component $\Gamma$ of the state space, the **$\Gamma$-network** $\mathcal G_\Gamma = (\mathcal S_\Gamma, \mathcal C_\Gamma, \mathcal R_\Gamma)$ consists of the reactions active somewhere on $\Gamma$; $\Gamma$ is **positive** if $\mathcal G_\Gamma = \mathcal G$. A stationary distribution $\pi_\Gamma$ on $\Gamma$ is **complex balanced** if, for every complex $y' \in \mathcal C_\Gamma$ and every $x \in \Gamma$,

$$\sum_{y \in \mathcal C_\Gamma} \pi_\Gamma(x - y' + y)\,\lambda_{y\to y'}(x - y' + y) = \sum_{y \in \mathcal C_\Gamma} \pi_\Gamma(x)\,\lambda_{y'\to y}(x),$$

i.e. the probability flux into states "at complex $y'$" balances the flux out, complex by complex. The system is **stochastically complex balanced** if some positive irreducible component carries a complex balanced stationary distribution.

**Theorem.** If an irreducible component $\Gamma$ carries a complex balanced stationary distribution, then $\mathcal G_\Gamma$ is weakly reversible. Under mass action, $\Gamma$ carries a complex balanced stationary distribution if and only if the deterministic $\Gamma$-system $(\mathcal G_\Gamma, \kappa_\Gamma)$ is complex balanced, and then

$$\pi_\Gamma(x) = M_\Gamma \prod_{i : S_i \in \mathcal S_\Gamma} \frac{c_i^{x_i}}{x_i!}, \qquad x \in \Gamma,$$

with $c$ a positive complex balanced equilibrium of the $\Gamma$-system and $M_\Gamma$ a normalizing constant.

**Corollary.** A stochastically complex balanced system has a weakly reversible network. A mass-action system $(\mathcal G,\kappa)$ is stochastically complex balanced if and only if its deterministic mass-action system is complex balanced; then every irreducible component carries a unique stationary distribution, which is complex balanced and of the product-Poisson form with a positive complex balanced equilibrium $c$ of $(\mathcal G,\kappa)$. Consequently $(\mathcal G,\kappa)$ is stochastically complex balanced for every choice of $\kappa$ if and only if $\mathcal G$ is weakly reversible with deficiency zero.

## Expansion

Summing the stochastic complex-balance equations over $y'$ recovers the global balance equations, so a complex balanced distribution is automatically stationary. For mass action, substituting the product-Poisson ansatz turns the stochastic equations into the deterministic complex-balance equations $\sum_{y\to y'} \kappa_{y\to y'} c^{y} = \sum_{y'\to y}\kappa_{y'\to y} c^{y'}$, giving the "if" direction (the Anderson–Craciun–Kurtz theorem). For "only if", the stochastic equations evaluated at states $x$ just above each complex $y'$ force ratios $\pi_\Gamma(x + e_i)/\pi_\Gamma(x)$ to factor as $c_i/(x_i+1)$, from which $c$ is read off and shown to be complex balanced. Weak reversibility follows because complex-wise flux balance forbids complexes that receive flux but cannot return it.

## Sources

- Daniele Cappelletti, Carsten Wiuf, "Product-form Poisson-like distributions and complex balanced reaction systems", arXiv (2015). Section 2 (active reactions, irreducible components), Section 4 (Definitions of $\Gamma$-system, complex balanced stationary distribution and stochastic complex balance; Theorem 4.3, Corollaries 4.4 and 4.5). <https://doi.org/10.48550/arXiv.1507.02195>. Published version: SIAM Journal on Applied Mathematics 76(1) (2016), 411–432, <https://doi.org/10.1137/15m1029916>; locators above refer to the arXiv version.
