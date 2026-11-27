# Conditional stationary distribution after eliminating non-interacting species

Let $(\mathcal N, \lambda)$ be a stochastic reaction network (a continuous-time Markov chain on $\mathbb N_0^n$ whose jumps are the reaction vectors $y' - y$, with intensities $\lambda_{y \to y'}(x)$), with species split as $\mathcal S = \mathcal Z \cup \mathcal U$, $\mathcal U = \{U_1, \dots, U_m\}$. Write $\rho(x) = \sum_i u_i U_i \in \mathbb N_0^m$ for the $\mathcal U$-part of a state $x = (z, u)$.

- $\mathcal U$ is a set of **non-interacting species** if every complex $y$ satisfies $\rho(y) = 0$ or $\rho(y) = U_i$ for one $i$: each complex contains at most one molecule of at most one species of $\mathcal U$, and none of them appear together.
- $\mathcal U$ consists of **intermediates** if moreover every complex containing a species of $\mathcal U$ is exactly that species, $y = \rho(y)$.
- The **reduced network** $(\mathcal N_{\mathcal U}, \lambda_{\mathcal U})$ is obtained by algebraic elimination: every walk $y + U_{i_0} \to \cdots \to y' + U_{i_q}$ through complexes of $\mathcal U$ that starts and ends outside $\mathcal U$ is collapsed into one reaction between core complexes, with an intensity given by the corresponding path weights.

Let $\Gamma$ be an irreducible component of $\mathcal N$ and $\Gamma_0 = \{x \in \Gamma : \rho(x) = 0\}$, the states with no non-interacting molecule present.

**Theorem.** Let $(\mathcal N, \lambda)$ be weakly reversible, let $\mathcal U$ be non-interacting and satisfy the condition that no reaction $y + U_i \to y' + U_i$ in the elimination has $y < y'$ or $y > y'$ componentwise, and let $\pi$ be a complex balanced stationary distribution on $\Gamma$ with $\Gamma_0 \neq \emptyset$. Then

1. $\Gamma_0$ is an irreducible component of $\mathcal N_{\mathcal U}$, or an at most countable disjoint union of such components;
2. the conditional law $\pi_0 = \pi(\cdot)/\pi(\Gamma_0)$ on $\Gamma_0$ is a stationary distribution of the reduced network (a linear combination of stationary distributions when $\Gamma_0$ splits into several components).

The conclusions also hold when $\mathcal N_{\mathcal U}$ has finitely many reactions. If $\mathcal U$ consists of intermediates, $\Gamma_0$ is a single irreducible component and $\pi_0$ is again *complex balanced* for $(\mathcal N_{\mathcal U}, \lambda_{\mathcal U})$; if $\pi$ is detailed balanced, $\pi_0$ is detailed balanced or a combination of detailed balanced laws on disjoint components.

## Depends on

- [Complex-balanced concentrations](../complex-balancing-and-the-deficiency-zero-theore/is-complex-balanced.md)
- [Non-explosivity of complex-balanced stochastic reaction networks](non-explosivity-of-complex-balanced-stochastic-reaction-networks.md)

## Expansion

Conditioning on $\rho = 0$ observes the chain only when no short-lived species is present. Between two such visits the chain makes an excursion through states carrying exactly one non-interacting molecule, and the net effect of an excursion is precisely one reaction of the reduced network; the complex balance equations of $\pi$ summed over these excursions give the stationarity equations of $\pi_0$. The order condition guarantees that from each state only finitely many excursion outcomes are reachable, so the elimination is well defined. The reduced network may be non-weakly reversible and have non-mass-action kinetics, yet the conditional law keeps the product form in the intermediate case.

## Sources

- L. Hoessly, C. Wiuf and P. Xia, "Asymptotic analysis for stationary distributions of multiscaled reaction networks", *Advances in Applied Probability* 58(3) (2025), 887–917, Section 2, Lemma 2.7, Lemma 3.1, Theorem 3.2, Corollary 3.3 and Propositions 3.5 and 3.6, <https://doi.org/10.1017/apr.2025.10040> (preprint arXiv:2402.02276).