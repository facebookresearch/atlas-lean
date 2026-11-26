# Renaming then substituting

Let $\rho : \mathbb{N} \to \mathbb{N}$ be a renaming of de
Bruijn variables, $\sigma$ a parallel substitution sending each index to a term of the simply
typed lambda calculus with references, and $t$ a term. Renaming $t$ by $\rho$ and then applying
$\sigma$ gives the same term as applying the substitution $\sigma \circ \rho$ to $t$.
