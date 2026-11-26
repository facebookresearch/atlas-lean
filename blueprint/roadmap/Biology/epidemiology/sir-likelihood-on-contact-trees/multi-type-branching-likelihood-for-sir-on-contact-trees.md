# Multi-type branching likelihood for SIR transmission on contact trees

**Model.** Each infected individual has $k$ downstream contacts (degree $k$ fixed, or random with law $w_k$) and is of type $(i, k)$ when $i$ of them are already infected. It infects each remaining susceptible contact at rate $\beta$ (total rate $(k-i)\beta$, moving to type $i+1$ and creating a new type-$0$ individual), and is removed at total rate $\gamma$, of which rate $\mu$ is removal without being observed; the remainder are observed (sampled) removals, which become the tips of the reported transmission tree.

**Theorem.**
1. *(Unobserved clades.)* For fixed degree $k$, the probability $E_i(t)$ that a type-$i$ individual leaves no sampled descendants over time $t$ satisfies, with $E_i(0) = 1$ and $E_{k+1} \equiv 0$,
$$\frac{dE_i}{dt} = \mu - \bigl(\gamma + (k-i)\beta\bigr)E_i + (k-i)\beta\, E_0 E_{i+1} .$$
2. *(Observed lineages.)* The density $D^i_j(t)$ that a type-$i$ lineage is observed as type $j$ satisfies
$$\frac{dD^i_j}{dt} = -\bigl(\gamma + (k-i)\beta\bigr)D^i_j + (k-i)\beta\, E_0 D^{i+1}_j + (k-i)\beta\, E_{i+1} D^0_j ,$$
and analogous equations hold for random degree with degree-averaged newborn quantities $\widehat E_0 = \sum_\ell w_\ell E_{0,\ell}$, $\widehat D^0_j = \sum_\ell w_\ell D^{(0,\ell)}_j$.
3. *(Likelihood.)* Conditioned on at least one observation and on the root time, the likelihood of a sampled tree is a sum over the root degree (weights $w_k$) and root state (weights given by the equilibrium type distribution $\pi_{i \mid k}$, normalised by $1 - E_{(i_0,k)}$) of products of $D$-terms along edges and branching factors $(k - i_m)\beta\,[D^{(i_m+1,k)}_{A}\widehat D^0_{B} + D^{(i_m+1,k)}_{B}\widehat D^0_{A}]$ at each transmission node, with daughters $A, B$.
4. *(Type equilibrium.)* The expected numbers of individuals of each type solve a linear ODE whose dominant eigenvalue has a positive spectral gap, so type frequencies converge to an equilibrium $\pi$; the equilibrium mean number of remaining susceptible contacts satisfies $S_\pi(k) \to k - 1$ as $k \to \infty$ and $\mathbb E[S_\pi] \approx \mathbb E[K] - 1$.

## Expansion

The model is a multi-type birth–death process in which the type of an infector increases with each transmission, so transmission potential declines as contacts are used up, unlike homogeneous-mixing birth–death models. The $E$ and $D$ equations are backward Kolmogorov equations obtained by conditioning on the first event in a short interval: removal (observed or not), or infection of a contact, after which the parent lineage and the newborn evolve independently. Because the tree records individuals as nodes and transmissions as edges, no sequence data or molecular clock is needed; the item-4 limit recovers the classical fact that on a tree one neighbour of a typical infected lineage is its infector.

## Sources

- A. Okolie, J. Müller, E. Akarawakc, I. Ajiboye, "Multi-type branching inference on contact trees with application to COVID-19", arXiv:2606.19405 (2026), Propositions 2.1, 2.2, 2.3, 2.4, 2.5 and 2.6, Corollary 2.7, Theorem 3.1, <https://doi.org/10.48550/arXiv.2606.19405>.
