# Opening independently conserved species: absolute concentration robustness and monostationarity

Let $G$ be a mass-action reaction network on species $\mathcal{X} = \{X_1,\dots,X_n\}$. A set $\mathcal{E} = \{X_{i_1},\dots,X_{i_k}\}$ of species is *independently conserved* if there are conservation laws $L_1,\dots,L_k \in \mathbb{R}^n$ (vectors orthogonal to the stoichiometric subspace) such that $X_{i_j}$ has nonzero coefficient in $L_j$ and zero coefficient in $L_l$ for $l \ne j$; enzymes with their enzyme-substrate complexes are the typical example. The *open network* $G_{\mathcal{E} \rightleftharpoons 0}$ adds $X \rightleftharpoons 0$ for every $X \in \mathcal{E}$ (all previously closed). The *projected network* $G_{-\mathcal{E}}$ deletes the species of $\mathcal{E}$ from every complex (a complex equal to $X \in \mathcal{E}$ becomes $0$) and removes self-loops. $\operatorname{cap}_{pos}(H)$ is the supremum over rate constants and compatibility classes of the number of positive steady states.

**Theorem (emergence of absolute concentration robustness).** If $\mathcal{E}$ is independently conserved in $G$, then either neither $G$ nor $G_{\mathcal{E} \rightleftharpoons 0}$ has a positive steady state, or $G$ has one and $G_{\mathcal{E} \rightleftharpoons 0}$ has absolute concentration robustness in every $X \in \mathcal{E}$, with steady-state value

$$x_X = \frac{\kappa_{0 \to X}}{\kappa_{X \to 0}}.$$

If some $X \in \mathcal{E}$ is only partially opened with inflow $0 \to X$ but no outflow, the opened network has no steady states.

**Theorem (monostationarity transfer).** If $\mathcal{E}$ is independently conserved in $G$, then $\operatorname{cap}_{pos}(G_{\mathcal{E} \rightleftharpoons 0}) \le \operatorname{cap}_{pos}(G_{-\mathcal{E}})$. In particular, if $G_{-\mathcal{E}}$ is monostationary, so is $G_{\mathcal{E} \rightleftharpoons 0}$.

**Corollary.** For every $n \ge 1$, the sequential distributive $n$-site phosphorylation cycle with both enzymes $E, F$ opened is monostationary, $\operatorname{cap}_{pos} \le 1$, and it has absolute concentration robustness in each opened enzyme. Opening enzymes therefore destroys the bistability that opening substrates preserves.

## Depends on

- [Substrate opening preserves multistationarity of the n-site phosphorylation cycle](substrate-opening-preserves-multistationarity-of-the-n-site-phosphorylation-cycle.md)
- [Deficiency-zero theorem, weakly reversible case](../../complex-balancing-and-the-deficiency-zero-theore/exists-unique-equilibrium.md)

## Expansion

Summing the steady-state equations of $G_{\mathcal{E} \rightleftharpoons 0}$ against the conservation law $L_j$ cancels all internal reactions (they conserve $L_j$) and leaves only the inflow and outflow of $X_{i_j}$, because $X_{i_j}$ is the only opened species appearing in $L_j$; hence $\kappa_{0\to X} - \kappa_{X\to 0} x_X = 0$ at every positive steady state. With the enzyme levels pinned to these constants, the remaining equations are those of the projected network with the enzyme concentrations absorbed into the rate constants, so steady states of the open network inject into steady states of $G_{-\mathcal{E}}$. For the phosphorylation cycle every bimolecular complex contains $E$ or $F$, so the projected network is monomolecular (complexes $S_i$, $ES_i$, $FS_i$), weakly reversible, with one linkage class and $3n+1$ complexes against a $3n$-dimensional stoichiometric subspace; its deficiency is zero, so it is monostationary.

## Sources

- Praneet Nandan, Beatriz Pascual-Escudero, Diego Rojas La Luz, "Multistationarity in semi-open Phosphorylation-Dephosphorylation Cycles", *Bulletin of Mathematical Biology* 88(11) (2026), 217, Definitions 2.8, 2.12 and 2.13, Theorems 4.1, 4.4 and 4.9, Corollary 4.13, <https://doi.org/10.1007/s11538-026-01771-8> (preprint arXiv:2511.10609).
