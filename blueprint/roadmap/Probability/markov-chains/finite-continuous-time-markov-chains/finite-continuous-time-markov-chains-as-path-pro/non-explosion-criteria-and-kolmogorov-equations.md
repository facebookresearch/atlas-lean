# Non-explosion criteria and Kolmogorov equations on a countable state space

Let $Q$ be a stable conservative $Q$-matrix on a countable set $I$, with exit rates $q_i=-q_{ii}$, and let $X$ be its [minimal chain](minimal-ctmc-on-a-countable-state-space.md) with jump chain $(Y_n)$, jump times $J_n$ and explosion time $\zeta=\sup_nJ_n$. Fix an initial state $i$.

1. **Characterization.** $\mathbb P_i(\zeta=\infty)=1$ if and only if $\sum_{n\ge0}1/q_{Y_n}=\infty$ $\mathbb P_i$-almost surely, with $1/0=\infty$.
2. **Sufficient conditions.** The chain started at $i$ does not explode if any of the following holds:
   - (a) $\sup_{j\in I}q_j<\infty$;
   - (b) $i$ is recurrent for the jump chain;
   - (c) there are $c\ge0$ and $V:I\to[0,\infty)$ with finite sublevel sets $\{V\le m\}$ for every $m$, such that $\sum_jq_{kj}V(j)$ converges and $\sum_jq_{kj}V(j)\le c\,V(k)$ for every $k\in I$.
3. **Kolmogorov equations.** If the chain does not explode from any state, its transition function $P(t)=(p_{jk}(t))$ is honest, $\sum_kp_{jk}(t)=1$ for all $j$ and $t$, and it satisfies both the backward equation $P'(t)=QP(t)$ and the forward equation $P'(t)=P(t)Q$, entrywise, with $P(0)=I$.

Example: the linear birth–death chain on $\{0,1,2,\ldots\}$ with rates $q_{n,n+1}=bn$ and $q_{n,n-1}=dn$ ($b,d\ge0$) does not explode, by criterion (c) with $V(n)=n$: $\sum_jq_{nj}V(j)=(b-d)n\le b\,V(n)$.

## Depends on

- [Minimal continuous-time Markov chain on a countable state space](minimal-ctmc-on-a-countable-state-space.md)

## Expansion

A full proof page must establish the following.

- Item 1: given the jump chain, $\zeta=\sum_nS_{n+1}$ with independent exponential terms of rates $q_{Y_n}$, and such a sum is finite almost surely if and only if $\sum_n1/q_{Y_n}<\infty$.
- Items 2(a) and 2(b) from item 1; item 2(c) by stopping at the exit times from the finite sets $\{V\le m\}$, a Dynkin-formula and Gronwall estimate $\mathbb E_i[V(X_{t\wedge\tau_m})]\le V(i)e^{ct}$, and the bound $\mathbb P_i(\tau_m\le t)\le V(i)e^{ct}/\inf_{\{V>m\}}V$.
- Item 3: honesty from non-explosion and the row-sum identity of the minimal chain; the backward equation from the minimal construction; the forward equation from the last-jump decomposition, with justification of the termwise differentiation and of the convergence of $\sum_jp_{kj}(t)q_{jl}$.
- The linear birth–death example.

## Sources

- J. R. Norris, *Markov Chains*, Cambridge University Press (1997), <https://www.statslab.cam.ac.uk/~jrn10//Markov/>, Theorem 2.7.1 and Section 2.8 (statement and proof).
