# Error bounds for the N-intertwined mean field approximation

**Setting.** Each vertex $i$ of a finite set $V$ ($|V|=N$) has a state in a finite set $\mathcal S$ (e.g. S, I, R), and the joint state evolves as a Markov process in which at most one vertex changes at a time. Vertex $i$ moves from $s'$ to $s$ at rate $r^{(m)}_{\underline ji;(\underline{\tilde s},s')\to(\underline{\tilde s},s)}$ when the $m$-tuple $\underline j=(j_1,\dots,j_m)$ is in states $\underline{\tilde s}$ ($0\le m\le M$; $m=1$ is a network, $m\ge2$ a hypergraph or simplicial contagion). Let $\bar r^{(m)}_{\underline ji}$ be the total such rate, $\delta_i^{(m)}=\frac1{m!}\sum_{\underline j}\bar r^{(m)}_{\underline ji}$ the incoming rate, $\delta_{\max}=\max_{m\ge1,i}\delta_i^{(m)}$, $\tilde r_{ji}=\sum_{m\ge1}\frac1{m!}\sum_{\underline k\ni j}\bar r^{(m)}_{\underline ki}$ the influence of $j$ on $i$, and $\tilde r_{\max}=\max_{i,j}\tilde r_{ij}$; for $M=1$ write $R=(\bar r_{ji})$. With independent initial states, let $y_{i,s}(t)=\mathbb P(\xi_i(t)=s)$, and let $z_{i,s}(t)$ solve the closed **NIMFA** system obtained by replacing every joint probability by the product of marginals,

$$\frac{d}{dt}z_{i,s}=\sum_{m=0}^M\frac1{m!}\sum_{\underline j,\underline{\tilde s},s'}r^{(m)}_{\underline ji;(\underline{\tilde s},s')\to(\underline{\tilde s},s)}\,z_{i,s'}\prod_{l=1}^mz_{j_l,\tilde s_l},\qquad z_{i,s}(0)=y_{i,s}(0).$$

**Theorem (uniform error).**

$$\max_{i\in V,s\in\mathcal S}|y_{i,s}(t)-z_{i,s}(t)|\le2Mt\,e^{2M\delta_{\max}t}\,\tilde r_{\max}.$$

This is sharp in $\tilde r_{\max}$: take the SI process on an unweighted graph with symmetric adjacency matrix $(a_{ij})$, $\bar r_{ij}=a_{ij}/\bar d$ and average degree $\bar d\ge1$, pick a vertex $i$ with degree $d_i\ge\bar d$, and start with $i$ infected with probability $1/2$ and every other vertex susceptible; then $|y_{i,I}(1)-z_{i,I}(1)|\ge\frac1{32\bar d}$.

**Theorem (average error, $M=1$, $R=R^\top$).**

$$\frac1N\sum_i\max_s|y_{i,s}(t)-z_{i,s}(t)|\le4t^2e^{3\delta_{\max}t}\,\frac1N\sum_m(R^2)_{mm}=4t^2e^{3\delta_{\max}t}\,\frac{\|R\|_F^2}{N},$$

and also $\le4t^2e^{3\|R\|_2t}\big(\frac1N\sum_m(R^2)_{mm}^2\big)^{1/2}$. For the SI process with i.i.d. $\mathrm{Ber}(1/2)$ initial infections the average error is at least $\frac1{16N}\sum_{i,j}e^{-(\delta_i+\delta_j)}\bar r_{ji}^2$, so for $\delta_{\max}=O(1)$ the average error is $\Theta(\|R\|_F^2/N)$. On an unweighted graph with $\bar r_{ij}=a_{ij}/\bar d$ and $\|R\|_2=O(1)$ the error is therefore of order $1/\bar d$, improving the earlier $1/\sqrt{\bar d}$ bound.

**Theorem (concentration).** For $\emptyset\ne\mathcal M\subseteq V$ and $M=1$, the fraction $\bar\xi^{\mathcal M}_s(t)$ of $\mathcal M$ in state $s$ satisfies $\mathrm{Var}\,\bar\xi^{\mathcal M}_s(t)\le|\mathcal M|^{-1}e^{2\|R\|_2t}$.

## Expansion

In the graphical construction, the state of $i$ at time $t$ depends only on its random *information set* $\mathcal H_i(t)$, grown backwards by adding every vertex whose potential interactions could have influenced it. NIMFA is exact on the event that the information sets feeding into $i$ from different neighbours are disjoint, which is coupled with an auxiliary branching structure whose marginals are $z_{i,s}$. The error is the probability that two such sets intersect: for one neighbour pair this costs a factor $\tilde r_{\max}$ (a single extra interaction), while on average over vertices it costs $(R^2)_{mm}$, the weight of a returning two-step path. The same intersection probabilities bound covariances, giving concentration of empirical averages even for subpopulations of sublinear size.

## Sources

- Dániel Keliger and Balázs Ráth, "Concentration and mean field approximation results for Markov processes on large networks", Stochastic Processes and their Applications 200 (2026), 105003, <https://doi.org/10.1016/j.spa.2026.105003>; numbering as in arXiv:2408.16908: Section 3 (model and NIMFA), Definition 4.2, Theorem 4.4, Theorems 4.14, 4.15, 4.16, 4.20 and 4.22, Corollary 4.21.
