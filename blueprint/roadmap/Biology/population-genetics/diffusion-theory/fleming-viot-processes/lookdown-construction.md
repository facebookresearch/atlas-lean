# The lookdown construction: almost-sure path convergence to the Fleming–Viot process

The finite shifting lookdown system, its consistency in the number of levels and its fixed-time exchangeability are stated in [the finite-level lookdown process](finite-level-lookdown-process-and-projective-con.md); the Kingman genealogy of its first $n$ levels is [the finite-level lookdown chain](../../../coalescent-theory/coalescents/finite-level-lookdown-chain-and-its-embedded-lam.md); the infinite system and its continuous directing process on a finite type space are [the infinite-level lookdown process](infinite-level-lookdown-process-finite-type-spac.md) and [the common directing process](common-directing-process-of-the-infinite-lookdow.md); and the $\Lambda$-lookdown with its directing process is the programme [infinite lookdown, de Finetti limit and the Λ-Fleming–Viot process](../../../coalescent-theory/coalescents/infinite-lookdown-de-finetti-limit-and-lambda-fl.md). This page states the remaining result, Birkner's Theorem 1.5.5, whose assumptions differ from those pages in three ways.

1. Type space. $E$ is a Borel subset of $\mathbb{R}$, possibly infinite or uncountable; for example $E = [0, 1]$.
2. Mutation. Every level mutates according to $B\phi(x) = \frac\theta2\int_0^1 (\phi(h(x, u)) - \phi(x))\,du$ (Birkner, (1.25)) with $\theta \ge 0$ and $h : E \times [0, 1] \to E$ measurable, so that mutation events occur at the bounded rate $\theta/2$ per level; the infinite-alleles model $h(x, u) = u$ on $[0, 1]$ is included.
3. Convergence. The finite systems are the first $N$ levels of one infinite ordered system, driven by rate-one reproduction clocks $L_{ij}$ for $i < j$ (the type at level $i$ is inserted at level $j$ and the higher types shift up one level) and by the mutation Poisson measures, with an exchangeable initial sequence $(\tilde\eta_0(i))_{i \ge 1}$ independent of the drivers (Birkner, Remark 1.5.2 and (1.27)–(1.29)). The convergence is almost sure for these coupled empirical processes, not weak convergence of separately constructed systems.

Under these assumptions let $\tilde Z^{(N)}_t = N^{-1}\sum_{i=1}^N \delta_{\tilde\eta_t(i)}$. Then almost surely $\tilde Z^{(N)}$ converges as $N \to \infty$ in the Skorokhod space $D_{\mathcal M_1(E)}([0, \infty))$, with the weak topology on the space $\mathcal M_1(E)$ of probability measures, to a process $Z$ with continuous paths, the Fleming–Viot process with mutation operator $B$ (Theorem 1.5.5). At each fixed $t$, $Z_t$ is the almost-sure limit $\lim_{m \to \infty} m^{-1}\sum_{i=1}^m \delta_{\tilde\eta_t(i)}$ given by de Finetti's theorem (Remark 1.5.4).

## Depends on

- [The finite-level lookdown process: consistency, exchangeability and fixed-time sampling](finite-level-lookdown-process-and-projective-con.md)

## Proof depends on

- [de Finetti's theorem for exchangeable sequences in a standard Borel space](../../../../Probability/foundations/exchangeable-sequences/de-finetti-theorem-for-exchangeable-sequences-in.md)

## Expansion

1. The infinite ordered system on a Borel type space $E \subseteq \mathbb{R}$, as the system of Poisson-driven equations of Remark 1.5.2, and the identification of its first $N$ levels with [the finite-level lookdown process](finite-level-lookdown-process-and-projective-con.md); the finite-type case is [the infinite-level lookdown process](infinite-level-lookdown-process-finite-type-spac.md).
2. The fixed-time de Finetti limit $Z_t$ (Remark 1.5.4), from the fixed-time exchangeability of the levels.
3. The exponential concentration bound for averages of bounded exchangeable variables and its maximal version (Proposition 1.5.7).
4. Theorem 1.5.5: almost-sure convergence of $\langle f, \tilde Z^{(N)}_t\rangle$ for $f$ in the domain of $B$, first on the time grid $k/N^4$ and then uniformly on compact time intervals, and continuity of the limit paths; the finite-type case is [the common directing process](common-directing-process-of-the-infinite-lookdow.md).
5. Separate targets: weak convergence of the unordered Moran empirical processes when $Z^{(N)}_0 \to Z_0$ weakly (Corollary 1.5.6); the martingale problem of the limit (Theorem 1.5.8); the Kingman genealogy of the levels, already [the finite-level lookdown chain](../../../coalescent-theory/coalescents/finite-level-lookdown-chain-and-its-embedded-lam.md); and the $\Lambda$-lookdown of Berestycki, Sec. 3.3.1, already the programme [infinite lookdown, de Finetti limit and the Λ-Fleming–Viot process](../../../coalescent-theory/coalescents/infinite-lookdown-de-finetti-limit-and-lambda-fl.md).

## Sources

- Original result: P. Donnelly and T. G. Kurtz, Particle representations for measure-valued population models, Ann. Probab. 27 (1999), 166–205. <https://doi.org/10.1214/aop/1022677258> The construction follows Birkner, Sec. 1.5.
- M. Birkner, *Stochastic population models*, lecture notes, Johannes Gutenberg-Universität Mainz, 2025/26, <https://www.staff.uni-mainz.de/birkner/SPM2526/StochPopModels_25-26.pdf>, Secs. 1.4–1.5: (1.25), generator (1.27), Remarks 1.5.2 and 1.5.4, Theorem 1.5.5, Corollary 1.5.6, Proposition 1.5.7 and Theorem 1.5.8.
- N. Berestycki, *Recent Progress in Coalescent Theory*, Ensaios Matemáticos 16, Sociedade Brasileira de Matemática, 2009. <https://arxiv.org/abs/0909.3985>
