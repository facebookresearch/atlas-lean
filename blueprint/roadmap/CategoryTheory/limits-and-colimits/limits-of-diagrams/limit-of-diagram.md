# Limit of a diagram: a cone with the universal property

Let $\mathsf{J}$ and $\mathsf{C}$ be categories and $F\colon \mathsf{J} \to \mathsf{C}$ a functor, a *diagram* of shape $\mathsf{J}$. A *cone* $(L, \lambda)$ over $F$ is an object $L$ of $\mathsf{C}$ with morphisms $\lambda_j\colon L \to Fj$, one for each object $j$ of $\mathsf{J}$, such that $Ff \circ \lambda_i = \lambda_j$ for every morphism $f\colon i \to j$ of $\mathsf{J}$. The cone $(L, \lambda)$ is a *limit* of $F$ if for every cone $(c, \mu)$ over $F$ there is exactly one morphism $u\colon c \to L$ with $\lambda_j \circ u = \mu_j$ for every object $j$ of $\mathsf{J}$. A witness that $(L, \lambda)$ is a limit consists of such a morphism $u$ for each cone $(c, \mu)$, together with the facts that $u$ satisfies these equations and that every morphism satisfying them equals $u$. Since $u$ is unique, any two witnesses for the same cone are equal.

## Sources

- Emily Riehl, Category Theory in Context, Dover Publications, 2016.
- The mathlib Community, *mathlib4* at revision 56a005855ea17e0b0958f73ec801ae140b0a1679, for the limit property recorded as a structure and the uniqueness of that structure: `CategoryTheory.Limits.IsLimit`, https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Limits/IsLimit.lean#L49-L56, and `CategoryTheory.Limits.IsLimit.subsingleton`, https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Limits/IsLimit.lean#L78-L79.
