# Robust permanence from a Morse decomposition of the extinction set

**Setting.** The structured ecological map $X_{t+1} = X_t A(X_t)$ with species-wise growth rates $r_i(\mu)$, extinction set $S_0$ and $\delta$-perturbations as in [Robustly unsaturated boundary sets via Lyapunov exponents](robustly-unsaturated-boundary-sets-via-lyapunov-exponents.md). The model is *permanent* if there is $\eta > 0$ such that every orbit with all species present eventually stays in $\{x : \|x^i\| > \eta \ \forall i\}$, and *robustly permanent* if for some $\delta > 0$ all $\delta$-perturbations are permanent with a common $\eta$.

**Theorem.** Let $\{M_1, \dots, M_k\}$ be a Morse decomposition of $S_0 \cap G_A$, where $G_A$ is the global attractor.

1. (Hofbauer–So) The model is permanent iff each $M_j$ is unsaturated.
2. If every $M_j$ satisfies $\max_i r_i(\mu) > 0$ for all invariant $\mu$ supported on $M_j$, the model is robustly permanent.
3. The model and all of its submodels are robustly permanent if, for every ergodic $\mu$ supported in $S_0$, $r_i(\mu) > 0$ for each species $i$ not in $\operatorname{supp}\mu$; conversely, if $\Phi_A$ is $C^2$ and the model and all submodels are robustly permanent, this condition holds.

**Corollary (two species).** For $m = 2$ and $x \mapsto xA(x)$ of class $C^2$, the model is robustly permanent iff (a) $\max_i r_i(0) > 0$, where $r_i(0)$ is the dominant growth rate of species $i$ at the extinction state, (b) $r_2(\mu) > 0$ for every ergodic $\mu$ supported where only species $1$ is present, and (c) $r_1(\mu) > 0$ for every ergodic $\mu$ supported where only species $2$ is present.

So for two species, robust coexistence is exactly mutual invasibility: each species can invade every ergodic state of the other, including periodic and chaotic ones.

## Depends on

- [Robustly unsaturated boundary sets via Lyapunov exponents](robustly-unsaturated-boundary-sets-via-lyapunov-exponents.md)

## Expansion

Item 2 combines item 1 with the robust unsaturation criterion applied to each Morse set: a Morse decomposition persists under small perturbations, and each component stays unsaturated. Item 3 applies item 2 to the coarsest decomposition and the necessity result to each ergodic boundary measure. In the two-species case the boundary $S_0$ consists of the origin and the two single-species faces, and the hypotheses on ergodic measures there are exactly (a)–(c). The source applies the criterion to Lotka–Volterra difference equations, competitive metacommunities (species structured by patch), and an SIR epidemic model in which the primitivity assumption is relaxed.

## Sources

- G. Roth, P. L. Salceanu, S. J. Schreiber, "Robust permanence for ecological maps", arXiv:1603.05004 (2016): Definitions 2.1–2.2, Section 3.2 (Theorem 3.5 (Hofbauer–So), Theorem 3.6, Corollaries 3.8 and 3.9), Section 5 (applications). <https://doi.org/10.48550/arXiv.1603.05004> Published version: SIAM Journal on Mathematical Analysis 49.5 (2017): 3527-3549, <https://doi.org/10.1137/16M1066440>.
