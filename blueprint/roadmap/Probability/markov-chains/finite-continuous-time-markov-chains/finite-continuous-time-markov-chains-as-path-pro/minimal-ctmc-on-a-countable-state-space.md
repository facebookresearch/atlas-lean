# Minimal continuous-time Markov chain on a countable state space

Let $I$ be a countable set and $Q=(q_{ij})_{i,j\in I}$ a stable conservative $Q$-matrix: $q_{ij}\ge0$ for $i\ne j$, $q_i=-q_{ii}<\infty$, and $\sum_{j\ne i}q_{ij}=q_i$ for every $i$. Let $\partial\notin I$ be a cemetery state. The jump-chain and holding-time construction defines the minimal chain: let $(Y_n)_{n\ge0}$ be a discrete-time Markov chain with initial law $\lambda$ and jump matrix $\Pi$, where $\pi_{ij}=q_{ij}/q_i$ for $j\ne i$ and $\pi_{ii}=0$ when $q_i>0$, and $\pi_{ij}=\delta_{ij}$ when $q_i=0$; given $(Y_n)$, let $S_1,S_2,\ldots$ be independent holding times with $S_{n+1}$ exponential of rate $q_{Y_n}$ ($S_{n+1}=\infty$ when $q_{Y_n}=0$). With jump times $J_0=0$, $J_n=S_1+\cdots+S_n$ and explosion time $\zeta=\sup_nJ_n$, set

$$X_t=Y_n\quad\text{for }J_n\le t<J_{n+1},\qquad X_t=\partial\quad\text{for }t\ge\zeta .$$

Then $X$ is a right-continuous Markov process on $I\cup\{\partial\}$, absorbed at $\partial$, and its transition function $p_{ij}(t)=\mathbb P_i(X_t=j)$, $i,j\in I$, is the minimal nonnegative solution of the backward equation

$$p'_{ij}(t)=\sum_{k\in I}q_{ik}\,p_{kj}(t),\qquad p_{ij}(0)=\delta_{ij}:$$

every nonnegative solution $\tilde p$ satisfies $\tilde p_{ij}(t)\ge p_{ij}(t)$. The rows satisfy $\sum_jp_{ij}(t)=\mathbb P_i(\zeta>t)\le1$, with equality for all $t$ if and only if the chain started at $i$ does not explode.

Examples: the pure-birth chain on $\{1,2,\ldots\}$ with rates $q_{n,n+1}=\lambda_n$, started at $1$, explodes almost surely when $\lambda_n=n^2$, since $\sum_n1/\lambda_n<\infty$, and does not explode when $\lambda_n=n$, since $\sum_n1/\lambda_n=\infty$.

## Proof depends on

- [Path of a continuous-time Markov chain](ctmc-path.md)

## Expansion

A full proof page must establish the following.

- Measurability of the construction and the Markov property of $X$ (the countable-state analogue of the finite construction from the [path of a continuous-time Markov chain](ctmc-path.md)).
- The first-jump decomposition $p_{ij}(t)=e^{-q_it}\delta_{ij}+\int_0^tq_ie^{-q_is}\sum_{k\ne i}\pi_{ik}p_{kj}(t-s)\,ds$, its equivalence with the backward equation, and minimality by comparing any nonnegative solution with the probabilities $\mathbb P_i(X_t=j,\ t<J_n)$ by induction on $n$.
- The row-sum identity.
- The pure-birth examples: $\mathbb E_1\zeta=\sum_n1/\lambda_n$ when finite, and $\sum_n1/\lambda_n=\infty$ forces $\zeta=\infty$ almost surely.

## Sources

- J. R. Norris, *Markov Chains*, Cambridge University Press (1997), <https://www.statslab.cam.ac.uk/~jrn10//Markov/>, Sections 2.2–2.8, minimal chains and explosion (statement and proof).
