# Finite interacting particle systems: existence, graphical construction and voter duality

Let $\Lambda$ be a finite set of sites and $S$ a finite set of local states. For each site $x\in\Lambda$ and $s\in S$ let $c_x(\eta,s)\ge0$ be the rate at which configuration $\eta\in S^\Lambda$ changes its value at $x$ to $s\ne\eta(x)$. Then:

1. **Existence.** There is a unique continuous-time Markov chain on the finite set $S^\Lambda$ whose rate matrix has off-diagonal entries $q(\eta,\eta^{x,s})=c_x(\eta,s)$, where $\eta^{x,s}$ agrees with $\eta$ off $x$ and equals $s$ at $x$, and all other off-diagonal entries zero.
2. **Graphical construction.** Let $\bar c>0$ with $\bar c\ge\max_{x,\eta}\sum_{s}c_x(\eta,s)$ (if all rates vanish the chain is constant and any $\bar c>0$ gives the empty update). Attach to every site $x$ an independent Poisson process of rate $\bar c$ with independent uniform marks on $[0,1]$. At a point $t$ of the process at $x$ with mark $U$, replace $\eta_{t-}(x)$ by $s$ if $U$ lies in the $s$-th of disjoint intervals of lengths $c_x(\eta_{t-},s)/\bar c$, and do nothing otherwise. Started from any $\eta_0$, this defines almost surely a càdlàg path whose law is that of the chain in item 1.
3. **Voter model and duality.** Let $p(x,y)\ge0$ ($x\ne y$) be rates on $\Lambda$, $S$ arbitrary, and let the voter model update by: at rate $p(x,y)$, site $x$ adopts the current value at $y$. Build it from independent Poisson processes $N_{xy}$ of rates $p(x,y)$, one per ordered pair. For $t>0$ and $x\in\Lambda$, follow the arrows of these processes backwards in time from $(x,t)$: from site $z$ jump to $y$ at each point of $N_{zy}$ met while going back. This gives coalescing random walks $(\hat Y^{x,t}_u)_{0\le u\le t}$, $x\in\Lambda$, each with jump rates $p(z,y)$, which move independently until they meet and together afterwards, and almost surely

    $$\eta_t(x)=\eta_0\bigl(\hat Y^{x,t}_t\bigr)\qquad\text{for all }x\in\Lambda .$$

    In particular, for $S=\{0,1\}$ and every $A\subseteq\Lambda$, $\mathbb P^{\eta_0}(\eta_t\equiv1\text{ on }A)=\mathbb P(\eta_0\equiv1\text{ on }A_t)$, where $A_t$ is the set of positions at time $t$ of coalescing random walks started from the points of $A$.

The Moran model with $N$ individuals and types in $S$ is the voter model on $\Lambda=\{1,\ldots,N\}$ with $p(x,y)$ constant, and its dual is the coalescing random walk on the complete graph.

## Proof depends on

- [Path of a continuous-time Markov chain](ctmc-path.md)
- [Superposition](../../../point-processes/poisson-processes/add.md)

## Expansion

A full proof page must establish the following.

- Item 1 from the finite-state theory of rate matrices.
- Item 2: thinning and [superposition](../../../point-processes/poisson-processes/add.md) of Poisson processes; the total number of clock rings on $[0,T]$ is finite almost surely, so the path is defined by finitely many updates; the jump rates of the resulting process at $\eta$ are $c_x(\eta,s)$, which identifies its law with that of the [path of a continuous-time Markov chain](ctmc-path.md) with the same rate matrix.
- Item 3: the backward paths are coalescing random walks by time reversal of Poisson processes on $[0,t]$; the identity follows by induction over the finitely many arrows in $[0,t]$; the duality formula is its consequence for indicator functions.
- The Moran-model instance.

## Sources

- T. M. Liggett, *Interacting Particle Systems*, Grundlehren der mathematischen Wissenschaften 276, Springer (1985), <https://link.springer.com/book/10.1007/b138374>, construction and voter-model duality (statement and proof).
