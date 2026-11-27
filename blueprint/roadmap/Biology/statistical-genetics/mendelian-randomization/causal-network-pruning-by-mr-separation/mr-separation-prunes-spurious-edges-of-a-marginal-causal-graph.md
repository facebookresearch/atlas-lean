# MR-separation prunes spurious edges of a marginal causal graph

Let $\mathcal G$ be the true causal DAG over phenotypes $X_1, \dots, X_d$ (with unobserved confounders), and let the marginal causal graph $\mathcal G_M$ have an edge $X_i \to X_j$ whenever $X_i$ has a nonzero total causal effect on $X_j$ (as estimated by pairwise bidirectional Mendelian randomization). Assume the causal Markov condition and faithfulness for $\mathcal G$, and that the genetic instruments used in multivariable Mendelian randomization (MVMR) are valid: relevant to at least one exposure, independent of unobserved confounders, and acting on the outcome only through the exposures. Then:

1. every edge and every collider of $\mathcal G$ is present in $\mathcal G_M$;
2. $\mathcal G$ and $\mathcal G_M$ have the same topological orderings;
3. if, for an edge $X_i \to X_j$ of $\mathcal G_M$, there is a sufficient separating set $S$ such that the MVMR direct effect of $X_i$ on $X_j$ adjusting for the genetic associations with $S$ is zero (written $X_i \perp_{\mathrm{MR}} X_j \mid S$, MR-separation), then $\mathcal G$ has no edge $X_i \to X_j$.

Candidate separating sets are all nodes on open paths from $X_i$ to $X_j$, a minimal sufficient adjustment set together with all mediators, or all other nodes except the colliders of $X_i$ and $X_j$. Testing the edges of $\mathcal G_M$ in topological order and iterating to convergence prunes $\mathcal G_M$ to an estimate of $\mathcal G$ using summary data only.

## Depends on

- [d-separation](../../../../ComputerScience/machine-learning/probabilistic-graphical-models/causal-bayesian-networks/dseparated.md)

## Expansion

A direct edge implies a nonzero total effect, and a total effect $X_i \to X_j$ requires a directed path, so $\mathcal G_M$ contains the transitive closure of $\mathcal G$; this gives statements 1 and 2. MVMR regresses the SNP–outcome associations on the SNP–exposure associations of $X_i$ and of the adjustment set, which estimates the direct effect of $X_i$ on $X_j$ not mediated by $S$; valid instruments make this unconfounded even with latent confounders, which is where MR-separation differs from d-separation. A zero direct effect for a sufficient set that blocks every mediated path and introduces no collider bias rules out a direct edge.

## Sources

- L. Hou, Z. Geng, Z. Yuan, X. Shi, C. Wang, F. Chen, H. Li and F. Xue, "MRSL: a causal network pruning algorithm based on GWAS summary data", Briefings in Bioinformatics 25 (2024) bbae086, <https://doi.org/10.1093/bib/bbae086>, PMCID PMC10940843. Assumptions 1–3, Lemmas 1–2, Definition 1, Theorem 1 and model (1).
