# Replicator dynamics of trait frequencies in a large metapopulation

**Setting.** A metapopulation has $K$ demes of $N$ individuals with a heritable trait in $\mathbb{R}^d$. Each deme follows a Moran process with selection; mutation and migration are rare enough that each deme is monomorphic except during brief fixation events. Let $\alpha(y,x)$ be the probability that a single individual of trait $y$ fixes in a deme of residents with trait $x$. On the slow time scale, a deme with trait $x$ switches to trait $y$ at rate

$$N\theta(x)\,\alpha(y,x)\,Q(x,dy) \;+\; N^2\lambda(x,y)\,\alpha(y,x)\,\mu_t(dy),$$

the first term from mutation (rate $\theta$, kernel $Q$) and the second from migrants drawn from the current metapopulation trait distribution $\mu_t$ with migration rate $\lambda$.

**Theorem.**

1. (*Propagation of chaos.*) As $K\to\infty$, the empirical trait distribution converges in law to the solution of a nonlinear (McKean–Vlasov) equation started from the limit of the initial empirical distributions; the limit is deterministic when that initial limit is deterministic (for example for i.i.d. initial traits), and in a homogeneous metapopulation with i.i.d. initial traits, finitely many tagged demes become independent copies of a time-inhomogeneous pure-jump Markov process driven by the limiting distribution.
2. (*Replicator dynamics.*) Without mutation, if the metapopulation is homogeneous and initially carries finitely many traits $x^1,\dots,x^n$ with mean weights $\bar w^i_t$, then

$$\frac{d\bar w^i_t}{dt} = \bar w^i_t \sum_{j=1}^n a_{ij}\,\bar w^j_t, \qquad a_{ij} = G(x^i,x^j),$$

$$G(y,x) = N^2\big(\lambda(x,y)\,\alpha(y,x) - \lambda(y,x)\,\alpha(x,y)\big),$$

a conservative replicator equation with antisymmetric payoff matrix ($a_{ji}=-a_{ij}$).
3. (*Invasion.*) If $\bar w^{i^\star}_0>0$ and $a_{i^\star j}>0$ for all $j\ne i^\star$, then $\bar w^{i^\star}_t\to1$: trait $x^{i^\star}$ takes over the metapopulation.

## Proof idea

Each deme is a single "particle" whose trait jumps through successful migration or mutation, with rates depending on the global trait distribution; this mean-field interaction gives propagation of chaos as the number of demes grows. In the two-trait comparison, demes of trait $x$ convert to $y$ at rate $N^2\lambda(x,y)\alpha(y,x)$ times the frequency of $y$ and convert back at the reverse rate, so the net flux is the antisymmetric fitness $G$. Antisymmetry preserves $\sum_i\bar w^i=1$, and a trait beating every other trait pairwise increases its weight until fixation. Rescaling mutation steps to be small then yields a canonical equation for the mean trait.

## Sources

- A. Lambert, H. Leman, H. Morlon and J. Tchouanti, "Evolution of a trait distributed over a large fragmented population: propagation of chaos meets adaptive dynamics", Journal of Mathematical Biology 92 (2026), article 70, <https://doi.org/10.1007/s00285-026-02371-9>. Numbering as in the preprint arXiv:2503.13154v1, <https://arxiv.org/abs/2503.13154v1>: Proposition 3.1, Theorem 4.1, Corollaries 4.1–4.2 and 5.1–5.2.
