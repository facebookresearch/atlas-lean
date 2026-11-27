# Λ-asymmetric Moran model and its ancestral selection graph

**Model.** A population of $N$ individuals has types $\oplus$ (fitter) and $\ominus$. At rate $1$ a uniformly chosen individual reproduces; given its type, a strength is drawn and each other individual independently dies and is replaced by an offspring of the reproducer with that probability. The two strength laws are coupled through a finite measure $\Lambda$ on $\Delta = \{(y,z) \in [0,1]^2 : y + z \le 1\}$: a $\ominus$ reproducer uses strength $y$ and a $\oplus$ reproducer uses $y + z$, so $\oplus$ has larger reproductive bursts, more frequent ones, or both. Let $X^N_t$ be the frequency of $\ominus$.

**Theorem.**
1. *(Ancestral selection graph and duality.)* Tracing potential ancestors backwards, neutral arrows are followed by every type and selective arrows only by $\oplus$. The number of potential ancestors $A^N$ is a Markov chain with jumps $n \mapsto n - k$ ($k = 1,\dots,n-1$) at rate

$$\frac nN\int_\Delta\binom{n-1}{k}y^k(1-y)^{n-1-k}\Lambda(dy,dz) + \Big(1 - \frac nN\Big)\int_\Delta\binom{n}{k+1}y^{k+1}(1-y)^{n-k-1}\Lambda(dy,dz)$$

and $n \mapsto n+1$ at rate $\big(1 - \frac nN\big)\int_\Delta\big[(1-y)^n - (1-y-z)^n\big]\Lambda(dy,dz)$, and $\mathbb E_x\big[S_0(X^N_t, n)\big] = \mathbb E_n\big[S_0(x, A^N_t)\big]$ with $S_0(x,n) = \binom{Nx}{n}/\binom{N}{n}$.
2. *(Scaling limits.)* Let now $\Lambda$ be any measure on $\Delta$ (possibly infinite) with $\int_\Delta(y^2 + z)\,\Lambda(dy,dz) < \infty$, fix $x\in[0,1]$ and $a\in(0,1/2)$, and let $\Lambda^{(N)}=\Lambda|_{\Delta_N}$ with $\Delta_N=\{(y,z)\in\Delta: y^2>N^{-a}\}$, a finite measure. Let $X^N$ be the frequency process of the Λ-asymmetric Moran model with $N$ individuals and reproduction measure $\Lambda^{(N)}$, started from $\lfloor xN\rfloor/N$, and $A^N$ its ancestral process. Then, with no time change, $X^N$ converges weakly in $D([0,T],[0,1])$ to the unique strong solution of the jump SDE

$$Y_t = x + \int_0^t\!\int_0^1\!\int_\Delta\Big(y(1-Y_{s-})\mathbf 1_{\{u \le Y_{s-}\}} - (y+z)Y_{s-}\mathbf 1_{\{u > Y_{s-}\}}\Big)\tilde N(ds,du,dy,dz) - \int_\Delta z\,\Lambda(dy,dz)\int_0^tY_s(1-Y_s)\,ds,$$

with $\tilde N$ the compensated Poisson random measure of intensity $dt\,du\,\Lambda(dy,dz)$, and $A^N$ converges weakly in $D([0,T],\mathbb N)$ to the branching–coalescing chain with $m \mapsto m - k + 1$ at rate $\int_\Delta\binom mk y^k(1-y)^{m-k}\Lambda(dy,dz)$ ($k \ge 2$) and $m \mapsto m + 1$ at rate $\int_\Delta\big[(1-y)^m - (1-y-z)^m\big]\Lambda(dy,dz)$; the two limits are moment dual, $\mathbb E_x[Y_t^n] = \mathbb E_n[x^{A_t}]$.

## Expansion

Because a $\oplus$ event of strength $y+z$ can be realized as a neutral event of strength $y$ plus an extra selective layer of strength $z$, the two reproduction laws live on one graphical representation. Selective arrows are potential parent relations that matter only if the potential parent is $\oplus$, which produces the branching in the ancestral process: with $m$ lineages, a branch is added when at least one lineage is hit by the selective layer but none by the neutral layer, which is the rate $(1-y)^m - (1-y-z)^m$. Unlike Kingman-type selection, the limit frequency process has jumps, and its fixation probability admits a semi-explicit Griffiths-type representation.

## Sources

- Adrián González Casanova, Noemi Kurt and José Luis Pérez, "The ancestral selection graph for a Λ-asymmetric Moran model", Theor. Popul. Biol. 159 (2024), 91–107, <https://doi.org/10.1016/j.tpb.2024.02.010>. Numbering follows the arXiv version, arXiv:2306.00130 (2023): Definition 2.1, Proposition 3.3, Proposition 4.5, Corollary 4.6 and Propositions 6.1, 6.3, 6.4, 6.5, <https://doi.org/10.48550/arXiv.2306.00130>.
