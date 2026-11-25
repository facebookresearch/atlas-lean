# Convergence to equilibrium for irreducible non-explosive countable chains with an invariant law

Let $Q$ be a stable conservative irreducible $Q$-matrix on a countable set $I$ whose [minimal chain](minimal-ctmc-on-a-countable-state-space.md) is non-explosive from every state (for example by the [non-explosion criteria](non-explosion-criteria-and-kolmogorov-equations.md)), and let $P(t)=(p_{ij}(t))$ be its transition function. Suppose $\pi$ is a probability vector on $I$ with $\pi Q=0$, that is, $\sum_i\pi_iq_{ij}=0$ for every $j$. Then:

1. every state is positive recurrent;
2. $\pi$ is the unique stationary law: $\pi P(t)=\pi$ for all $t\ge0$, and every probability vector $\mu$ with $\mu P(t)=\mu$ for all $t$ equals $\pi$;
3. for every initial state $i$,

    $$\bigl\|\mathbb P_i(X_t\in\cdot)-\pi\bigr\|_{\mathrm{TV}}=\sup_{A\subseteq I}\bigl|p_{iA}(t)-\pi(A)\bigr|\longrightarrow0\qquad(t\to\infty).$$

No aperiodicity hypothesis is needed in continuous time. When $I$ is finite the non-explosion hypothesis holds automatically and the statement is the ergodic theorem for finite irreducible chains. If positive numbers $\theta_i$ satisfy detailed balance $\theta_iq_{ij}=\theta_jq_{ji}$ and $\sum_i\theta_i<\infty$, then $\pi=\theta/\sum_i\theta_i$ satisfies $\pi Q=0$ and the statement applies.

## Depends on

- [Minimal continuous-time Markov chain on a countable state space](minimal-ctmc-on-a-countable-state-space.md)
- [Non-explosion criteria and Kolmogorov equations on a countable state space](non-explosion-criteria-and-kolmogorov-equations.md)

## Proof depends on

- [Triangle inequality for total variation distance](../../../convergence-of-measures/total-variation-distance/total-variation-dist-triangle.md)

## Expansion

A full proof page must establish the following.

- Items 1 and 2: for an irreducible $Q$, non-explosion together with an invariant distribution $\pi Q=0$ is equivalent to positive recurrence, and then $\pi_j=1/(q_jm_j)$ with $m_j$ the mean return time to $j$; uniqueness follows.
- Item 3: pointwise convergence $p_{ij}(t)\to\pi_j$, from the discrete skeleton $P(\delta)$, which is irreducible and aperiodic because $p_{jj}(\delta)\ge e^{-q_j\delta}>0$, or by coupling; then total-variation convergence by Scheffé's lemma, and monotonicity of the distance in $t$ by contraction under the semigroup.
- The finite irreducible case, and the detailed-balance corollary: $\sum_i\theta_iq_{ij}=\theta_j\sum_iq_{ji}=0$, the series converging absolutely because $\sum_{i\ne j}q_{ji}=q_j<\infty$.

## Sources

- J. R. Norris, *Markov Chains*, Cambridge University Press (1997), Sections 3.5–3.6, invariant distributions and convergence to equilibrium (statement and proof).
