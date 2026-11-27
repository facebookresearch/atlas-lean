# Group-key conditional independence and reduced knockoff construction

**Definition (group-key conditional independence).** Let $X = (X_1, \dots, X_p)$ be partitioned into groups $A_1, \dots, A_g$. The law of $X$ has the group-key conditional independence property if each group splits into disjoint *key* and *non-key* parts, $A_\gamma = A_\gamma^\star \cup A_\gamma^\dagger$, such that

$$X_\gamma^\dagger \perp\!\!\!\perp X_{-\gamma} \mid X_\gamma^\star, \qquad \gamma = 1, \dots, g .$$

The key variables carry all dependence across groups. Unlike a hidden Markov structure, the sizes of $A_\gamma^\star$ and $A_\gamma^\dagger$ are arbitrary, and the non-key variables within a group need not be conditionally independent of each other.

**Construction.** Write $X^\star = (X_1^\star, \dots, X_g^\star)$.

1. Generate valid group knockoffs $\tilde X^\star$ for $X^\star$, with groups $A_\gamma^\star$.
2. For each $\gamma$, compute the conditional law $F_\gamma$ of $X_\gamma^\dagger$ given $X^\star$.
3. Draw $\tilde X_\gamma^\dagger \sim F_\gamma(\cdot \mid \tilde X^\star)$ independently across $\gamma$.
4. Output $\tilde X = \bigl((\tilde X_1^\star, \tilde X_1^\dagger), \dots, (\tilde X_g^\star, \tilde X_g^\dagger)\bigr)$.

Multiple knockoff copies are obtained by generating several $\tilde X^\star$ in step 1 and independent draws in step 3.

**Theorem 1 (validity).** If $X$ has group-key conditional independence with respect to $\{A_\gamma\}$, the output $\tilde X$ is a valid group knockoff of $X$ for the groups $\{A_\gamma\}$.

**Theorem 2 (ME optimality is inherited).** Under the same hypothesis, if $(X^\star, \tilde X^\star)$ minimizes the maximum-entropy criterion $L^\star_{\mathrm{ME}}(S^\star) = \log\det\bigl((G^\star_{S^\star})^{-1}\bigr)$ for the key variables, then the law of $(X, \tilde X)$ produced by the construction minimizes $L_{\mathrm{ME}}(S) = \log\det(G_S^{-1})$ over all group knockoffs of $X$.

**Cost.** Optimization runs over the key blocks only, with $\sum_\gamma |A_\gamma^\star|^2$ free parameters instead of $\sum_\gamma |A_\gamma|^2$. Applied to genotype correlation matrices, with key variants chosen heuristically so that the property holds approximately, this gave a reported 10–100x speedup with slightly higher power and no loss of FDR control in simulations.

## Depends on

- [Second-order group knockoffs and their optimality criteria](second-order-group-knockoffs-and-optimality-criteria.md)

## Expansion

Validity reduces to the key variables. Swapping a union of groups exchanges $(X_\gamma^\star, X_\gamma^\dagger)$ with $(\tilde X_\gamma^\star, \tilde X_\gamma^\dagger)$ for those $\gamma$. Since each non-key block depends on the rest only through the key variables, and the knockoff non-key block is drawn from the same conditional law given the knockoff keys, the joint law factorizes as (law of keys and their knockoffs) $\times \prod_\gamma$ (conditional laws). The first factor is swap-invariant by step 1 and the conditional factors permute among themselves. Heuristically, for ME the entropy of $(X, \tilde X)$ splits into the entropy of $(X^\star, \tilde X^\star)$ plus conditional entropies of the non-key blocks. The conditional terms are fixed by the law of $X$, so maximizing the first term maximizes the total. Hence the cheap construction is exactly the ME-optimal one when the structure holds.

## Sources

- B. B. Chu, J. Gu, Z. Chen, T. Morrison, E. Candès, Z. He, C. Sabatti, "Second-order group knockoffs with applications to genome-wide association studies", Bioinformatics 40 (2024) btae580, Section 4, Definition 1, Algorithm 2, Theorems 1 and 2, <https://doi.org/10.1093/bioinformatics/btae580> (PMC11639161).
