# Kingman limit of genealogies of non-neutral particle systems under fast mutation

**Model.** A population of $N$ particles evolves in discrete generations on a Polish space $\mathcal X$. Generation $k$ has locations $X_k=(X_k(1),\dots,X_k(N))$. Given fitness (potential) functions $g_k:\mathcal X\to(0,\infty)$ and mutation kernels $M_k(x,dy)$ with densities, each child $i$ of generation $k+1$ picks a parent index $a_k(i)\in\{1,\dots,N\}$ with marginal law
$$\mathbb P\big(a_k(i)=m\mid X_k\big)=\frac{g_k(X_k(m))}{\sum_{v=1}^N g_k(X_k(v))},$$
the joint law of $(a_k(1),\dots,a_k(N))$ being fixed by a *resampling scheme*; the child is then placed at a point drawn from $M_k(X_k(a_k(i)),\cdot)$. This is a Wright–Fisher model with selection ($g_k$ = fitness, $M_k$ = mutation) and also the structure of a sequential Monte Carlo (SMC) algorithm.

Label time backwards from a terminal generation $0$. For $n\le N$ sampled particles, the genealogical process $(\bar G^{N,n}_k)_{k\ge0}$ is the partition of $\{1,\dots,n\}$ whose blocks are the samples with a common ancestor $k$ generations back. It is not Markov when fitness is inherited, because family sizes in different generations are dependent.

**Theorem (sufficient conditions for a Kingman limit).** Let $c_N(\xi,\ell,j;k)$ be $\binom{|\xi|}{2}^{-1}$ times the conditional probability, given all locations $\mathbf X=(X_k)_k$, that at least one merger occurs in generation $k$ given the labelled partition $(\xi,\ell)$ at generation $j$ and no merger in between, and let $\tau_N(\xi,\ell,j;t)=\min\{s\ge j:\sum_{k=j+1}^s c_N(\xi,\ell,j;k)\ge t\}$ be the induced random time change. Suppose that, almost surely as $N\to\infty$: the one-generation merger rates and their sums of squares up to $\tau_N$ vanish; the conditional probability that the merger at time $\tau_N$ is a specific binary merger $\xi\prec\eta$ is asymptotically $c_N$ (so multiple and simultaneous mergers are negligible and all pairs are equally likely); and $\tau_N<\infty$ with probability tending to one. Then for every fixed $n$, the genealogical process run on the concatenated time scale $\tau_N(t)$ converges weakly in the Skorokhod $J_1$ topology to Kingman's $n$-coalescent $(\Pi^n_t)_{t\ge0}$.

**Proposition (multinomial resampling under strong mixing).** Suppose there exist $\gamma\ge1$ and $f:\mathcal X\to(0,\infty)$ with
$$\frac{f(y)}{\gamma}\le g_k(x)M_k(x,y)\le\gamma f(y)\qquad\text{for all }x,y\in\mathcal X,\ k\ge1 .$$
Then multinomial resampling satisfies the conditions of the theorem, and the time scale obeys, almost surely,
$$\Big\lfloor\frac{Nt}{\gamma^4}\Big\rfloor\le\tau_N(t)\le\frac{(n+1)n(n-1)}{6}\,\lceil\gamma^4Nt\rceil ,$$
so coalescence of lineages happens on a time scale of order $N$ generations.

## Expansion

The proof works in a quenched setting: conditionally on all particle locations, lineages perform inhomogeneous coalescing random walks, so the holding time in each partition state can be analysed exactly through the conditional merger probabilities $c_N$, and the time change $\tau_N$ turns these holding times into asymptotically unit-rate exponential clocks per pair. Gluing the holding times state by state yields the jump chain and holding times of Kingman's coalescent. The key assumption is fast mixing: the mutation kernel must erase information about fitness between successive mergers, so that the parent of a merger being fitter than average does not bias the next merger. The strong mixing bound on $g_kM_k$ makes every particle's chance of being a given lineage's parent comparable to $1/N$ up to a factor $\gamma^2$, which gives the time-scale bounds. This replaces an earlier argument that relied on a "random assignment" formula for transition probabilities given family sizes, which fails when fitness is hereditary.

A further observation: ordering of the expected pair-coalescence probabilities $\frac{1}{(N)_2}\sum_i\mathbb E[(\nu_k(i))_2]$ between resampling schemes does not imply ordering of the merger probabilities $c_N$; with $N=4$, three lineages and parent weights $(1-3z,z,z,z)$, $z\le1/12$, stratified resampling forces a merger with probability $1$, while multinomial resampling gives $1-18z^2+48z^3$.

## Depends on

- [Holding times and jump chain of Kingman's n-coalescent are independent](../partition-valued-kingman-coalescent/holding-times-and-jump-chain-of-kingman-s-n-coal.md)

## Sources

- Jere Koskela, Paul A. Jenkins, Adam M. Johansen and Dario Spanò, "Genealogical processes of sequential Monte Carlo methods and other non-neutral population models under rapid mutation", arXiv:2406.16465 (2024), Section 2, Theorem 1; Section 3.1, Proposition 1; Section 3.4. <https://doi.org/10.48550/arXiv.2406.16465>
