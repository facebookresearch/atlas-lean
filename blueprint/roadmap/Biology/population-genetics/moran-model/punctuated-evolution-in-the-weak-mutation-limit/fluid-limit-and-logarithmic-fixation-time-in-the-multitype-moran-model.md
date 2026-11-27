# Fluid limit and logarithmic fixation time in the multitype Moran model

**Model.** A well-mixed population of constant size $N$ consists of finitely many types $i\in I$ with distinct fitnesses $f_i>0$ (bounded, of order one). Let $x_i(t)\in\{0,1/N,\dots,1\}$ be the fraction of type $i$. Each individual of type $i$ reproduces at rate $f_i$ and its offspring replaces an individual chosen uniformly at random, so $x_i\to x_i+1/N$, $x_j\to x_j-1/N$ at rate $Nf_ix_ix_j$; there is no mutation. Its deterministic limit is the competitive-exclusion (replicator) system on the simplex $\Delta_I$,

$$\dot x_i=x_i\big(f_i-\bar f(x)\big),\qquad \bar f(x)=\sum_j f_jx_j,$$

whose solutions are $x_i(t)=x_i(0)e^{f_it}/\sum_jx_j(0)e^{f_jt}$. Let $i^*$ be the fittest type present, $f^*=\max_if_i$, $f^{**}$ the second largest fitness, and $s=f^*-f^{**}$ the selection coefficient. Write $\Phi_t$ for the ODE flow, $D^*(t)=\sup_{u\le t}\|x(u)-\Phi_ux(0)\|_1$, and call events $A_N$ *stretch-exponentially unlikely* if $\mathbb P(A_N)\le Ce^{-N^\gamma}$ for some $C,\gamma>0$.

**Theorem.** Assume $|I|\le N^\mu$ for some $\mu<1/2$. Then:

1. There are $c,\beta>0$ such that the event that no type goes extinct before $c\ln N$ and yet $D^*(c\ln N)>N^{-\beta}$ is stretch-exponentially unlikely.
2. For every $\delta<\beta$ there is $C>0$ (one can take $C=1/s$) such that, conditioned on non-extinction of $i^*$ and up to a stretch-exponentially unlikely event, $\|x(C\ln N)-e^{(i^*)}\|\le N^{-\delta}$.
3. There are $C',\alpha>0$ such that if $\|x(0)-e^{(i^*)}\|\le N^{-\delta}$ then $\mathbb P\big(x(C'\ln N)=e^{(i^*)}\big)>1-N^{-\alpha}$.
4. There is $p>0$ independent of $N$ such that type $i^*$ survives with probability at least $p$ from any state with $x_{i^*}(0)>0$.
5. For every $\delta\in(0,1)$, if $x_{i^*}(0)>N^{-\delta}$ then extinction of $i^*$ is stretch-exponentially unlikely.

So a new fittest type either dies out while rare or, once it reaches a fraction $N^{-\delta}$, follows the ODE and fixes in time of order $\ln N/s$.

## Expansion

Write $x(t)-\Phi_tx(0)$ as a martingale term plus an integral of the drift difference. Each coordinate martingale has jumps $1/N$ and predictable quadratic variation at most $tF/N$ ($F$ a fitness bound), so an exponential martingale inequality makes deviations above $N^{-\beta}$ by time $c\ln N$ stretch-exponentially rare, and a Gronwall-type bound on the drift keeps the error from amplifying over a logarithmic horizon (part 1). Since the ODE converges to $e^{(i^*)}$ at exponential rate $s$, time $\ln N/s$ brings the state within $N^{-\delta}$ of fixation (part 2). Parts 3-5 compare $x_{i^*}$ with a birth-death chain jumping up at rate $Nf^*x(1-x)$ and down at rate $Nf^{**}x(1-x)$, an asymmetric random walk with positive escape probability and logarithmic absorption time.

## Depends on

- [Weak-mutation limit justifies the origination-fixation chain](../../../molecular-evolution/origination-fixation-dynamics/weak-mutation-limit-justifies-the-origination-fi.md)
- [One-step transition probabilities of the Moran process](../moran-prob.md)
- [Solution of the replicator equation](../../../population-dynamics/replicator-dynamics/is-solution.md)

## Sources

- Bakhtin Y, Katsnelson MI, Wolf YI, Koonin EV. Evolution in the weak-mutation limit: Stasis periods punctuated by fast transitions between saddle points on the fitness landscape. *Proc. Natl. Acad. Sci. USA* 118 (2021). <https://doi.org/10.1073/pnas.2015665118> (PMCID: PMC7848522). Eq. (1)-(5) and Theorem 1, with Lemmas 1-3 in its proof.
