# Stochastic deficiency zero theorem

Let $\mathcal G$ be a reaction network with deficiency $\delta = |\mathcal C| - \ell - s$ ($\ell$ linkage classes, $s$ the dimension of the stoichiometric subspace), modelled stochastically on $\mathbb N^n$. A reaction $y \to y'$ is **terminal** if every directed path in the reaction graph starting with it lies in a closed directed path; let $\mathcal S^*$ be the species of the terminal subnetwork. The network is **essential** if its state space is a union of closed irreducible components. Use the notions of [active reactions, $\Gamma$-networks and positive components](stochastic-complex-balance-is-equivalent-to-deterministic-complex-balance.md).

**Theorem (boundary behaviour).** Suppose $\delta = 0$. If $x$ lies in an irreducible component $\Gamma$ and the reaction $y \to y'$ is active on $x$ ($y \le x$), then $y \to y'$ is terminal; in particular $\mathcal G_\Gamma$ is a weakly reversible deficiency-zero subnetwork of the terminal network. Under mass action the stationary distribution on $\Gamma$ is

$$\pi_\Gamma(x) = M_\Gamma \prod_{i : S_i \in \mathcal S^*} \frac{c_i^{x_i}}{x_i!}, \qquad x \in \Gamma,$$

where $c$ is a positive complex balanced equilibrium of the terminal system.

**Theorem (stochastic deficiency zero theorem).** Suppose $\delta = 0$.

1. If $\mathcal G$ is not weakly reversible, there are no positive irreducible components.
2. If $\mathcal G$ is weakly reversible, then $\mathcal G$ is essential, and under mass action every irreducible component carries a unique stationary distribution (of product-Poisson form).

These mirror the deterministic deficiency zero theorem: absence of positive equilibria corresponds to absence of positive irreducible components, and a unique positive equilibrium per stoichiometric class corresponds to a unique stationary distribution per irreducible component.

## Depends on

- [Stochastic complex balance is equivalent to deterministic complex balance](stochastic-complex-balance-is-equivalent-to-deterministic-complex-balance.md)

## Expansion

Deficiency never increases on passing to subnetworks, so every $\Gamma$-network has deficiency zero. A path argument shows that if $y_1 \to \cdots \to y_q$ is a directed path and $x \ge y_1$, then $x + y_q - y_1$ is reachable from $x$; on a closed irreducible component this forces every active reaction to lie on a cycle, i.e. to be terminal, and a deficiency-zero network whose reactions are all reachable back is weakly reversible. A weakly reversible deficiency-zero $\Gamma$-system is complex balanced for every choice of rate constants, so the equivalence of stochastic and deterministic complex balance yields the product-form stationary law. For a non-weakly-reversible network, some reaction is non-terminal, so it cannot be active on a closed component, which excludes positive components.

## Sources

- Daniele Cappelletti, Carsten Wiuf, "Product-form Poisson-like distributions and complex balanced reaction systems", arXiv (2015). Section 3 (Lemma 3.2, Theorems 3.4 and 3.5), Section 4 (Proposition 4.2, Theorems 4.6 and 4.7), Appendix A (Lemmas A.1–A.3). <https://doi.org/10.48550/arXiv.1507.02195>. Published version: SIAM Journal on Applied Mathematics 76(1) (2016), 411–432, <https://doi.org/10.1137/15m1029916>; locators above refer to the arXiv version.
