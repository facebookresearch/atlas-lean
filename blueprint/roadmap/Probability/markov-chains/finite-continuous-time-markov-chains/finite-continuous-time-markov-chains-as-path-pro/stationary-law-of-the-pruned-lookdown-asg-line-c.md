# Stationary law of the pruned lookdown ancestral selection graph line count

Let $\sigma>0$, $\theta\ge0$ and $\nu_0+\nu_1=1$ with $\nu_0,\nu_1\ge0$, and let $Q$ be the rate matrix on $\mathbb N_0$ of the [pruned lookdown ancestral selection graph line count](pruned-lookdown-asg-line-counting-generator-froz.md): $q(0,1)=\sigma$ and, for $n\ge1$, $q(n,n+1)=(n+1)\sigma$, $q(n,n-1)=n(n+1)+n\theta\nu_1+\theta\nu_0$ and $q(n,n-\ell)=\theta\nu_0$ for $2\le\ell\le n$. Then:

1. the minimal chain of $Q$ is non-explosive from every state;
2. it is irreducible and positive recurrent on $\mathbb N_0$;
3. it has a unique stationary law $\rho=(\rho_n)_{n\ge0}$, characterized as the unique probability vector with $\rho Q=0$.

## Depends on

- [Generator of the pruned lookdown ancestral selection graph line count](pruned-lookdown-asg-line-counting-generator-froz.md)
- [Non-explosion criteria and Kolmogorov equations on a countable state space](non-explosion-criteria-and-kolmogorov-equations.md)

## Proof depends on

- [Convergence to equilibrium for irreducible non-explosive countable chains with an invariant law](convergence-to-equilibrium-for-irreducible-nonex.md)
- [Normalized balance weights of a birth–death rate sequence](../../birth-death-processes/birth-death-balance-weights.md)

## Expansion

A full proof page must establish the following.

- Item 1 by the Lyapunov criterion of the [non-explosion criteria](non-explosion-criteria-and-kolmogorov-equations.md) with $V(n)=n+1$: the only upward jump has size one and rate $(n+1)\sigma$, so $\sum_mq(n,m)V(m)\le\sigma V(n)$.
- Irreducibility: upward rates are positive because $\sigma>0$, and $q(n,n-1)\ge n(n+1)>0$ for $n\ge1$.
- Positive recurrence and existence of $\rho$: for instance by a drift (Foster–Lyapunov) bound, since the downward rate grows quadratically while the upward rate grows linearly, or by the stochastic domination of $L$ by the ancestral selection graph line count minus one, which is positive recurrent; then uniqueness of $\rho$ from [convergence to equilibrium for irreducible non-explosive chains](convergence-to-equilibrium-for-irreducible-nonex.md).
- In the special case $\theta\nu_0=0$ the chain is a birth–death chain with birth rates $(n+1)\sigma$ and death rates $n(n+1)+n\theta\nu_1$, and $\rho$ is given by its [normalized balance weights](../../birth-death-processes/birth-death-balance-weights.md).
- The boundary case $\sigma=0$ lies outside the statement: then $0$ is absorbing, every state leads to it, and $\delta_0$ is the unique stationary law, but the chain is not irreducible.

## Sources

- U. Lenz, S. Kluth, E. Baake, A. Wakolbinger, *Looking down in the ancestral selection graph: a probabilistic approach to the common ancestor type distribution*, Theoretical Population Biology 103 (2015), 27–37, <https://www.techfak.uni-bielefeld.de/ags/bm/publications/Looking_down_ASG.pdf>, Section 5.2, equation (9), Remark 3 and the following paragraph (unique equilibrium distribution $\rho$), and equation (13) ($\rho Q=0$) (statement and proof).
