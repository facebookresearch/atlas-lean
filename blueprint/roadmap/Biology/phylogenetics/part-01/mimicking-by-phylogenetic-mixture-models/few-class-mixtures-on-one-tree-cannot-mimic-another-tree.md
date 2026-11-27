# Few-class mixtures on one tree cannot mimic another tree

**Models.** For a $\kappa$-state general continuous-time substitution model on a leaf-labeled tree $T$ (any strictly positive root distribution, an irreducible rate matrix $Q_e$ and length $t_e \ge 0$ on each edge, possibly different per edge), $\mathcal M_T$ is the set of site-pattern distributions it produces. The **open model** $\mathcal M_T^{+} \subseteq \mathcal M_T$ requires every internal edge length to be positive. For a multiset $\mathcal T = \{T_1,\dots,T_r\}$ the **mixture model** $\mathcal M_{\mathcal T}$ consists of all $\sum_i s_i p_i$ with $p_i \in \mathcal M_{T_i}$, $s_i \ge 0$, $\sum_i s_i = 1$; $\mathcal M^{+}_{\mathcal T}$ uses $p_i \in \mathcal M^{+}_{T_i}$, and $\mathcal M^{++}_{\mathcal T}$ additionally requires all $s_i > 0$.

A mixture $\mathcal M^*_{\mathcal T}$ **weakly mimics** $\mathcal M^*_{\mathcal S}$ if the two share a distribution, **strongly mimics** it if $\dim(\mathcal M^*_{\mathcal T}\cap\mathcal M^*_{\mathcal S}) = \dim\mathcal M^*_{\mathcal S}$, and **completely mimics** it if $\mathcal M^*_{\mathcal S} \subseteq \mathcal M^*_{\mathcal T}$.

**Theorem.** Let $\mathcal T$ consist of $\kappa - 1$ copies of a tree $T_1$ and $\mathcal S = \{T_2\}$. Under the $\kappa$-state general continuous-time model, $\mathcal M_{\mathcal T}$ and $\mathcal M_{\mathcal S}^{+}$ have no distribution in common unless $T_1$ is a refinement of $T_2$.

For nucleotide models ($\kappa = 4$, including GTR), a mixture of up to three classes on one topology therefore never reproduces the data of a different unmixed topology with positive internal branches. The property propagates: weak mimicking is preserved under fusing trees along common ends, and for quartets differing by an NNI move, mimicking between $r$ copies of $T_{12|34}$ and $s$ copies of $T_{13|24}$ lifts to $r$ copies of $T$ versus $s$ copies of $T'$ for any trees $T, T'$ differing by an NNI.

## Expansion

Every edge transition matrix is either the identity or nonsingular with positive entries (Lemma 1). For a quartet and its split $12|34$, the flattening of a distribution on $T_{12|34}$ into a $\kappa^2\times\kappa^2$ matrix has rank at most $\kappa$, so a mixture of $\kappa - 1$ such classes has flattening rank at most $\kappa(\kappa-1) < \kappa^2$. A distribution on $T_{13|24}$ with positive internal edge has a full-rank $12|34$ flattening, because it factors through Kronecker products of nonsingular transition matrices and a nonsingular diagonal matrix. Hence the quartet case (Lemma 2); restricting to four-leaf subsets that separate $T_1$ from a non-coarsening $T_2$ gives the theorem. If $T_1$ refines $T_2$, setting the extra edge lengths to $0$ shows $\mathcal M^+_{\mathcal S} \subseteq \mathcal M_{\mathcal T}$, so the exception is real.

## Sources

- Elizabeth S. Allman, John A. Rhodes, Seth Sullivant, "When do phylogenetic mixture models mimic other phylogenetic models?", arXiv (2012). Section "Phylogenetic mixture models" (definitions, Lemma 1), Section "Results" (Theorem 1, mimicking definitions, Propositions 1–2, Theorem 2), Appendix (flattenings, Lemma 2). <https://doi.org/10.48550/arXiv.1202.2396>. Published version: Systematic Biology 61(6) (2012), 1049–1059, <https://doi.org/10.1093/sysbio/sys064>; locators above refer to the arXiv version.
