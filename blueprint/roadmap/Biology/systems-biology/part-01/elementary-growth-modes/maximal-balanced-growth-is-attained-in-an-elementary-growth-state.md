# Maximal balanced growth is attained in an elementary growth state

**Setting.** A self-fabricating cell has $m$ metabolites with concentrations $x \in \mathbb{R}^m_{\ge 0}$, $n$ enzymes with concentrations $e_j$ catalysing reactions at rates $e_j f_j(x)$, and ribosomes $r$ that synthesize enzyme $j$ (and, for $j = n+1$, ribosomes themselves) at rate $r\,\alpha_j\, g_j(x)$, where $\alpha = (\alpha_1, \dots, \alpha_{n+1}) \ge 0$ is the ribosome allocation, $|\alpha| = \sum_j \alpha_j \le \lambda \le 1$, and $f_j, g_j$ are kinetic rate laws. Metabolic stoichiometry, precursor consumption by protein synthesis and a constant cell density determine the specific growth rate $\mu$, and all concentrations are diluted by growth. At **balanced growth** (all concentrations constant), eliminating $e$ and $r$ leaves equations that are *linear in $\alpha$* for fixed $(x, \mu)$:

$$B(x, \mu)\, \alpha = \mu\, u_{m+1}, \qquad \alpha \ge 0, \qquad |\alpha| \le \lambda,$$

where $B(x,\mu) \in \mathbb{R}^{(m+1)\times(n+1)}$ has one row per metabolite with nonzero concentration and a last row $(0, \dots, 0, g_{n+1}(x))$ expressing ribosome self-replication $\alpha_{n+1} g_{n+1}(x) = \mu$; $u_{m+1}$ is the last unit vector. Assume $B$ has full row rank for the $(x, \mu)$ considered.

**Definitions.** For fixed $(x, \mu)$, $P_{x,\mu} = \{ \alpha \in \mathbb{R}^{n+1} : B(x,\mu)\alpha = \mu u_{m+1},\ \alpha \ge 0 \}$ is a convex polytope. Its vertices are the **elementary growth states** (EGSs) at $(x, \mu)$. Two EGSs, possibly at different $(x, \mu)$, are equivalent when they have the same support; the equivalence classes are the **elementary growth modes** (EGMs), the minimal sets of enzymes that can sustain balanced growth.

**Theorem.**
1. Every balanced-growth solution with growth rate $\mu$ and metabolite concentrations $x$ is a convex combination of EGSs at the same $(x, \mu)$.
2. An EGS uses at most as many metabolic enzymes as there are independent metabolites with nonzero concentration, with equality when its feasible basis equals its support.
3. An EGS whose support equals its feasible basis extends continuously to EGSs of the same EGM for all $(x, \mu)$ in a neighbourhood.
4. For every $\lambda$, the maximal balanced growth rate $\max_{x,\alpha} \{ \mu : B(x,\mu)\alpha = \mu u_{m+1},\ \alpha \ge 0,\ |\alpha| \le \lambda \}$ is attained at an EGS, hence by a single EGM.

## Expansion

(1) is the Minkowski–Weyl statement that a bounded polyhedron is the convex hull of its vertices; convex combinations of EGSs at *different* growth rates need not be solutions, because $B$ depends on $\mu$. (2) holds because a vertex is a basic feasible solution: it has a feasible basis $D$ with $B_D(x,\mu)$ square and invertible, $|D|$ equals the number of independent rows, and $D$ must contain the ribosome column. (3) follows from continuity of $B_D(x,\mu)^{-1}\mu u_{m+1}$ in $(x,\mu)$, which keeps the positive entries positive nearby. For (4), fix the optimal $x$ and let $\mu_{\max}$ be optimal. If $P_{x,\mu}$ is nonempty for some $\mu > \mu_{\max}$, then by continuity every point of $P_{x,\mu_{\max}}$ has $|\alpha| \ge \lambda$, so the optimum minimizes the linear function $|\alpha|$ over $P_{x,\mu_{\max}}$, and a linear function attains its minimum at a vertex. Otherwise growth stops because some allocation would have to become negative, and any vertex of the nonempty polytope $P_{x,\mu_{\max}}$ is optimal. Growth maximization thus selects one minimal enzyme set, the self-fabrication analogue of the result that flux-balance optima can be taken at elementary flux modes; with $k$ additional linear enzymatic constraints the optimum is a convex combination of at most $k+1$ EGMs.

## Sources

- D. H. de Groot, J. Hulshof, B. Teusink, F. J. Bruggeman and R. Planqué, "Elementary growth modes provide a molecular description of cellular self-fabrication", PLoS Computational Biology 16 (2020), e1007559, Results (Eqs. (22)–(31), Definitions 1–2, Theorems 1–4), <https://doi.org/10.1371/journal.pcbi.1007559>, PMCID: PMC7004393.
