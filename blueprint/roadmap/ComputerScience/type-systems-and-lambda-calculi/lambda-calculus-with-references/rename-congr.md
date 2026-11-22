# Renaming respects pointwise equality

Let $\rho, \rho' : \mathbb{N} \to \mathbb{N}$ be
renamings of de Bruijn variables with $\rho(x) = \rho'(x)$ for every $x \in \mathbb{N}$. Then for
every term $t$ of the simply typed lambda calculus with references, renaming $t$ by $\rho$ gives
the same term as renaming $t$ by $\rho'$.
