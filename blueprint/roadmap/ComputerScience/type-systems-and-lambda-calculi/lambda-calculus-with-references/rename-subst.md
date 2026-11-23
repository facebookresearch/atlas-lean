# Substituting then renaming

Let $\rho : \mathbb{N} \to \mathbb{N}$ be a renaming of de
Bruijn variables, $\sigma$ a parallel substitution sending each index to a term of the simply
typed lambda calculus with references, and $t$ a term. Applying $\sigma$ to $t$ and then renaming
the result by $\rho$ gives the same term as applying to $t$ the substitution that sends each
index $x$ to the renaming of $\sigma(x)$ by $\rho$.
