# A union of flux-mode supports induces a flux-consistent subnetwork

**Setting.** A metabolic network $\mathcal{N}$ has stoichiometric matrix $S \in \mathbb{R}^{m \times n}$ over reaction set $\mathcal{N} = \{1, \dots, n\}$, with irreversible reactions $\mathcal{I} \subseteq \mathcal{N}$. A **mode** is a flux vector $v \in \mathbb{R}^n$ with

$$S v = 0, \qquad v_i \ge 0 \ \ (i \in \mathcal{I}), \qquad \ell \le v \le u .$$

Its support is $\operatorname{supp}(v) = \{ i : v_i \neq 0 \}$. A reaction is **blocked** if $v_i = 0$ for every mode, and a network with no blocked reaction is **(flux) consistent**. For $\mathcal{A} \subseteq \mathcal{N}$ the **induced subnetwork** keeps the columns of $S$ indexed by $\mathcal{A}$ (and the metabolites they touch).

**Theorem.** Let $\mathcal{V}$ be any set of modes of $\mathcal{N}$ and $\mathcal{A} = \bigcup_{v \in \mathcal{V}} \operatorname{supp}(v)$. Then the subnetwork induced by $\mathcal{A}$ is consistent.

**Context-specific reconstruction problem.** Given a core set $\mathcal{C} \subseteq \mathcal{N}$ of reactions known to be active in a tissue or condition (with $\mathcal{N}$ consistent), find

$$\min_{\mathcal{A} \subseteq \mathcal{N}} \ |\mathcal{A}| \quad \text{s.t. } \mathcal{C} \subseteq \mathcal{A} \text{ and the subnetwork induced by } \mathcal{A} \text{ is consistent.}$$

By the theorem this can be searched over sets of modes: minimize $\left|\bigcup_{v \in \mathcal{V}} \operatorname{supp}(v)\right|$ subject to $\mathcal{C} \subseteq \bigcup_{v \in \mathcal{V}} \operatorname{supp}(v)$. When all $r$ elementary modes are known, with binary support vectors $m_1, \dots, m_r \in \{0,1\}^n$, this is solved exactly by a mixed integer linear program with binary variables $x \in \{0,1\}^n$ (reaction $i$ is kept iff $x_i = 1$) and nonnegative real weights $y \in \mathbb{R}^r_{\ge 0}$ (elementary mode $j$ is selected iff $y_j > 0$), of the form

$$\min_{x,\,y} \ \mathbf{1}^\top x \quad \text{s.t.} \quad \kappa \sum_{j=1}^r y_j m_j \ \le \ x, \qquad \sum_{j=1}^{r} y_j m_j \ \ge \ \mathbf{1}_{\mathcal{C}},$$

where $\kappa > 0$ is a scaling factor that keeps the left side of the first constraint in $[0,1]^n$. The first constraint forces every reaction in a selected mode into $\mathcal{A} = \{ i : x_i = 1\}$, the second forces every core reaction to be covered by a selected mode, and minimization removes superfluous reactions, so at an optimum $\mathcal{A}$ is exactly the union of the selected supports.

## Expansion

For $v \in \mathcal{V}$ let $\tilde v$ be $v$ restricted to the coordinates in $\mathcal{A}$. Since $v_i = 0$ outside $\operatorname{supp}(v) \subseteq \mathcal{A}$, we have $S_{\mathcal{A}} \tilde v = S v = 0$ and $\tilde v$ still satisfies the sign and bound constraints, so $\tilde v$ is a mode of the induced subnetwork. Each $i \in \mathcal{A}$ lies in $\operatorname{supp}(v)$ for some $v \in \mathcal{V}$, so it carries nonzero flux in the corresponding $\tilde v$ and is not blocked. Every mode is a nonnegative combination of elementary modes, so restricting the search to elementary modes loses nothing; the mixed integer program encodes the covering version of that search. The general problem (empty core) contains minimum-cardinality elementary-mode search and is NP-hard, which motivates the linear-programming heuristics of the fastcore algorithm.

## Sources

- N. Vlassis, M. P. Pacheco and T. Sauter, "Fast reconstruction of compact context-specific metabolic network models", PLoS Computational Biology 10 (2014), e1003424, Methods (Theorem 1, Theorem 2, LP-7, LP-10, Box 1), <https://doi.org/10.1371/journal.pcbi.1003424>, PMCID: PMC3894152.
