# Equivalence of controlled and population-size-dependent branching processes

**Two models.** A *population-size-dependent branching process* (PSDBP) is a Markov chain on $\mathbb N_0$ with

$$Z_n=\sum_{i=1}^{Z_{n-1}}\xi_{n,i}(Z_{n-1}),$$

where, given $Z_{n-1}=z$, the $\xi_{n,i}(z)$ are i.i.d. copies of an offspring law $\xi(z)$ that depends on the current size. A *controlled branching process* (CBP) is a Markov chain with

$$\widetilde Z_n=\sum_{i=1}^{\widetilde\phi_n(\widetilde Z_{n-1})}\widetilde\xi_{n,i},$$

where a random number $\widetilde\phi_n(z)\stackrel d=\widetilde\phi(z)$ of individuals (the control function) reproduce with a fixed offspring law $\widetilde\xi$. Both describe density-regulated populations, for example Beverton–Holt or Ricker models with carrying capacity $K$. Two processes started from the same $z_0\ge1$ are *equivalent* if they have the same law, which for Markov chains means the same one-step law from every attainable state.

**Statement.**

1. Every PSDBP is a CBP (take $\widetilde\xi\equiv1$ and $\widetilde\phi(z)=\sum_{i=1}^z\xi_i(z)$). A CBP for which $0$ is attainable and $\mathbb P\big(\sum_{i=1}^{\widetilde\phi(0)}\widetilde\xi_i>0\big)>0$ is never equivalent to a PSDBP, since zero is absorbing for a PSDBP.
2. Call the control function $\widetilde Z$-divisible if $\widetilde\phi(0)=0$ and, for every attainable $z\ge1$, $\widetilde\phi(z)$ is $z$-divisible: $\widetilde\phi(z)\stackrel d=\sum_{i=1}^z\zeta_i(z)$ for i.i.d. $\zeta_i(z)$. Then the CBP is equivalent to a PSDBP, with offspring law $\xi(z)=\sum_{j=1}^{\zeta(z)}\widetilde\xi_j$.
3. Hence a CBP with Poisson control $\widetilde\phi(z)\sim\mathrm{Poi}(\psi(z))$ or negative-binomial control $\widetilde\phi(z)\sim\mathrm{NB}(\psi(z),q)$ is equivalent to a PSDBP if and only if $\psi(0)=0$. With binomial control $\widetilde\phi(z)\sim\mathrm{Bin}(\psi(z),q)$, $\psi(0)=0$ and $\psi(z)/z\in\mathbb N_0$ for all attainable $z\ge1$ suffice.
4. Divisibility of the control function is sufficient but not necessary, and infinite divisibility of the offspring law does not rescue a non-divisible control: with $\widetilde\phi(z)\sim\mathrm{Bin}(\psi(z),p(z))$, $p(z)\in(0,1)$, $\psi(z)\ge1$ for $z\ge1$, a non-$\widetilde Z$-divisible control and Poisson offspring $\widetilde\xi\sim\mathrm{Poi}(\lambda)$, no equivalent PSDBP exists; with geometric offspring $\widetilde\xi\sim\mathrm{Geom}(q)$ instead, $\psi(0)=0$ alone gives an equivalent PSDBP.

## Expansion

Equivalence reduces to asking whether the one-step law $\sum_{i=1}^{\widetilde\phi(z)}\widetilde\xi_i$ splits into $z$ i.i.d. pieces for every attainable $z$. A $z$-divisible control does this directly, by regrouping the reproducing individuals into $z$ i.i.d. families. The Poisson-offspring obstruction rests on the fact that a mixture of Poisson laws over a non-degenerate bounded mixing law is not infinitely divisible, while with geometric offspring the one-step law from $z$ is a sum of $\psi(z)$ i.i.d. zero-inflated geometric variables (a $\mathrm{Bernoulli}(p(z))$ indicator times a $\mathrm{Geom}(q)$ variable), which is infinitely divisible and so splits into $z$ i.i.d. pieces.

## Sources

- Peter Braunsteins, Sophie Hautphenne and James Kerlidis, "Linking population-size-dependent and controlled branching processes", Stochastic Processes and their Applications 181 (2025), 104556, <https://doi.org/10.1016/j.spa.2024.104556>; numbering as in arXiv:2308.01150: Lemma 3.1, Remark 3.2, Definition 3.3, Proposition 3.4, Corollaries 3.5–3.6, Propositions 3.7–3.8.
