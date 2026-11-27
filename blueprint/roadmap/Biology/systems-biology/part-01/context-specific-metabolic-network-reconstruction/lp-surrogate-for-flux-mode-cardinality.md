# Linear-programming surrogate for the cardinality of a flux mode

**Setting.** As for flux modes of a metabolic network with stoichiometric matrix $S \in \mathbb{R}^{m\times n}$: modes satisfy $Sv = 0$, $v_i \ge 0$ on irreversible reactions and $\ell \le v \le u$. Fix a flux threshold $\varepsilon > 0$ (a reaction is regarded as active when $|v_i| \ge \varepsilon$) and a set $\mathcal{J}$ of reactions whose fluxes are taken nonnegative (sign-flip columns of $S$ if needed). The cardinality of $v$ on $\mathcal{J}$ is

$$\operatorname{card}_{\mathcal{J}}(v) = \sum_{i \in \mathcal{J}} \theta(v_i), \qquad \theta(x) = \begin{cases} 1, & x > 0,\\ 0, & x = 0, \end{cases}$$

which is quasiconcave on $\mathbb{R}^{\mathcal{J}}_{\ge 0}$ and nonconvex in general.

**Surrogate.** Replace $\theta$ on $x \ge 0$ by the concave minorant-type approximation

$$\theta(x) \approx \min\{ x/\varepsilon,\ 1 \},$$

which agrees with $\theta$ at $x = 0$ and for $x \ge \varepsilon$. Introducing epigraph variables $z_i$ and rescaling by $\varepsilon$, maximizing the surrogate becomes the linear program

$$\max_{v,\,z} \ \sum_{i \in \mathcal{J}} z_i \quad \text{s.t.} \quad S v = 0, \quad v \in \text{bounds}, \quad z_i \le v_i,\ \ 0 \le z_i \le \varepsilon \ \ (i \in \mathcal{J}).$$

At an optimum, $z_i = \min\{v_i, \varepsilon\}$, and $\{ i \in \mathcal{J} : v_i \ge \varepsilon \}$ is a set of reactions that can be simultaneously active with flux at least $\varepsilon$.

**Sparse completion.** Given an active set $\mathcal{K}$ found this way and a penalty set $\mathcal{P}$ of reactions one prefers not to add, a mode dense in $\mathcal{K}$ and sparse in $\mathcal{P}$ is obtained by the $L_1$-minimization linear program

$$\min_{v} \ \sum_{i \in \mathcal{P}} |v_i| \quad \text{s.t.} \quad S v = 0, \quad v \in \text{bounds}, \quad v_i \ge \varepsilon \ \ (i \in \mathcal{K}),$$

with $|v_i|$ linearized by auxiliary variables. The fastcore algorithm alternates these two programs, adding $\operatorname{supp}(v)$ to the reconstructed set until every core reaction is covered, so the output is consistent by the union-of-supports theorem.

## Depends on

- [A union of flux-mode supports induces a flux-consistent subnetwork](union-of-mode-supports-gives-a-consistent-subnetwork.md)

## Expansion

The function $x \mapsto \min\{x/\varepsilon, 1\}$ is a minimum of two affine functions, hence concave, so its sum over $\mathcal{J}$ maximized over a polyhedron is a linear program after taking epigraphs. The surrogate never overstates cardinality on reactions whose flux reaches the threshold and gives partial credit $v_i/\varepsilon$ below it, so optimal solutions push as many fluxes as possible up to $\varepsilon$. The $L_1$ step is the standard convex proxy for minimizing the number of nonzeros outside $\mathcal{K}$, keeping each added mode, and hence the reconstructed network, compact.

## Sources

- N. Vlassis, M. P. Pacheco and T. Sauter, "Fast reconstruction of compact context-specific metabolic network models", PLoS Computational Biology 10 (2014), e1003424, Methods (Theorem 1, Theorem 2, LP-7, LP-10, Box 1), <https://doi.org/10.1371/journal.pcbi.1003424>, PMCID: PMC3894152.
