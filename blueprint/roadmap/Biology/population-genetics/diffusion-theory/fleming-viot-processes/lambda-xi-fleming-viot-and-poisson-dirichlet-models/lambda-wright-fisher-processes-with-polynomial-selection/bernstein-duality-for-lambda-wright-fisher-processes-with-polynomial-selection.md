# Bernstein duality for Λ-Wright–Fisher processes with polynomial selection

**Setting.** Let $\Lambda$ be a nonzero finite measure on $[0,1]$ and let $d$ be a real polynomial with $d(0)=d(1)=0$ and $\deg d\le m$ for some integer $m\ge 2$. The $\Lambda$-Wright–Fisher process with frequency-dependent selection is the $[0,1]$-valued pathwise unique strong solution $X$ of

$$
dX_t = d(X_t)\,dt + \sqrt{\Lambda(\{0\})X_t(1-X_t)}\,dW_t + \int_{(0,1]\times[0,1]} r\bigl(\mathbf 1_{\{u\le X_{t-}\}}(1-X_{t-}) - \mathbf 1_{\{u>X_{t-}\}}X_{t-}\bigr)\,\tilde N(dt,dr,du),
$$

where $W$ is a Brownian motion and $\tilde N$ an independent compensated Poisson measure with intensity $dt\times r^{-2}\Lambda(dr)\times du$.

Write $b_{i,n}(x)=\binom{n}{i}x^i(1-x)^{n-i}$ for the Bernstein basis and $B_n(x)=(b_{i,n}(x))_{i=0}^n$. A *selection decomposition* of $d$ is a pair $(\beta,p)$ with $\beta=(\beta_\ell)_{\ell=2}^m\in\mathbb{R}_+^{m-1}$ and $p=(p_{j,\ell})$, $p_{0,\ell}=0$, $p_{\ell,\ell}=1$, $p_{j,\ell}\in[0,1]$, such that

$$
d(x)=\sum_{\ell=2}^m \beta_\ell \sum_{i=0}^{\ell} b_{i,\ell}(x)\Bigl(p_{i,\ell}-\frac{i}{\ell}\Bigr).
$$

Interpretation: at rate $\beta_\ell$ an individual gathers $\ell$ potential parents, and if $j$ of them carry type $a$ the offspring is of type $a$ with probability $p_{j,\ell}$. **Every polynomial vanishing at $0$ and $1$ has infinitely many selection decompositions.**

**Bernstein coefficient process.** Put $\lambda_{n,k}=\int_{[0,1]} r^{k-2}(1-r)^{n-k}\Lambda(dr)$. For $v\in\mathbb{R}^{n+1}$ define $S^{n,\ell}v\in\mathbb{R}^{n+\ell}$ and $C^{n,k}v\in\mathbb{R}^{n-k+2}$ by

$$
(S^{n,\ell}v)_i=\mathbb{E}\bigl[p_{K_i,\ell}\,v_{i+1-K_i}+(1-p_{K_i,\ell})\,v_{i-K_i}\bigr],\qquad (C^{n,k}v)_i=\frac{i}{n-k+1}v_{i+k-1}+\Bigl(1-\frac{i}{n-k+1}\Bigr)v_i,
$$

with $K_i$ hypergeometric with parameters $(n+\ell-1,i,\ell)$. The Bernstein coefficient process $V$ on $\bigcup_n\mathbb{R}^{n+1}$ jumps from $v\in\mathbb{R}^{n+1}$ to $S^{n,\ell}v$ at rate $n\beta_\ell$ ($2\le\ell\le m$) and to $C^{n,k}v$ at rate $\binom{n}{k}\lambda_{n,k}$ ($2\le k\le n$); its leaf process is $L_t=\dim V_t-1$.

**Theorem (Bernstein duality).** For every selection decomposition $(\beta,p)$ of $d$, all $t>0$, $x\in[0,1]$, $n\in\mathbb{N}$ and $v\in\mathbb{R}^{n+1}$,

$$
\mathbb{E}_x\bigl[\langle B_n(X_t),v\rangle\bigr]=\mathbb{E}_v\bigl[\langle B_{L_t}(x),V_t\rangle\bigr].
$$

In particular $\mathbb{E}_x[X_t^n]=\mathbb{E}_{e_{n+1}}[\langle B_{L_t}(x),V_t\rangle]$.

**Recurrence and absorption.** Let $b(\beta)=\sum_{\ell=2}^m\beta_\ell(\ell-1)$ (effective branching rate) and $c(\Lambda)=\int_{[0,1]}|\log(1-r)|\,r^{-2}\Lambda(dr)$ (coalescence impact). If $\Lambda\ne\delta_1$, the leaf process is positive recurrent when $b(\beta)<c(\Lambda)$ and transient when $b(\beta)>c(\Lambda)$. The first and last entries of $V_t$ are constant in time; if $b(\beta)<c(\Lambda)$, then for all $a,b$ the process $V$ has a unique invariant law $\mu^{a,b}$ supported on vectors with first entry $a$ and last entry $b$, and the absorption probability $h(x)=\mathbb{P}_x(\lim_{t\to\infty}X_t=1)$ satisfies

$$
h(x)=\mathbb{E}\bigl[\langle B_{L_\infty}(x),V_\infty\rangle\bigr],\qquad V_\infty\sim\mu^{0,1},
$$

with $h(x)\in(0,1)$ for $x\in(0,1)$, so both boundary points are accessible.

## Depends on

- [Process-level selection duality with the ASG line-counting process](../../../selection-duality-and-general-one-dimensional-di/process-level-selection-duality-with-the-asg-lin.md)

## Expansion

The decomposition $(\beta,p)$ defines Moran models whose type-frequency processes converge to $X$; in the large-population limit their genealogy is a branching–coalescing graph (a generalized ancestral selection graph) in which each line splits into $\ell$ lines at rate $\beta_\ell$ and $k$-tuples merge at the $\Lambda$-coalescent rates. Colour the leaves independently with type $a$ with probability $x$ and propagate types from leaves to roots with the colouring rule $p$; the conditional probability that all $n$ roots are of type $a$ is a random polynomial, the ancestral selection polynomial, whose Bernstein coefficient vector evolves as $V$ (a branching event acts by $S^{n,\ell}$, a merger by $C^{n,k}$). Averaging gives the duality, which reduces to the classical moment duality when $V$ stays a unit vector. Both $S^{n,\ell}$ and $C^{n,k}$ are averaging operators preserving the end entries, which is why the invariant laws are indexed by the boundary values and why $V_\infty\sim\mu^{0,1}$ encodes fixation. The recurrence criterion compares the linear growth $b(\beta)n$ of branching with the asymptotic coalescence speed $c(\Lambda)n$ of the $\Lambda$-coalescent.

## Sources

- Fernando Cordero, Sebastian Hummel and Emmanuel Schertzer, "General selection models: Bernstein duality and minimal ancestral structures", *Ann. Appl. Probab.* 32(3) (2022), 1499–1556. <https://doi.org/10.1214/21-AAP1683>
- Preprint version (the locators in this item follow its numbering): Fernando Cordero, Sebastian Hummel, Emmanuel Schertzer, *General selection models: Bernstein duality and minimal ancestral structures*, arXiv (2019). Definitions 2.5, 2.12, 2.18; Theorem 2.6 (infinitely many selection decompositions); Theorem 2.14 (Bernstein duality); Corollary 2.15; Theorem 2.20 (classification of the leaf process); Proposition 2.24 (invariant distributions); Proposition 2.27 (absorption probabilities). <https://doi.org/10.48550/arXiv.1903.06731>
