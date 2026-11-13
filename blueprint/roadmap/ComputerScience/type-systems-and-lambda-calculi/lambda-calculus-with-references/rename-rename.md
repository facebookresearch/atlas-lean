# Composition of renamings

For all renamings $\rho, \rho' : \mathbb{N} \to \mathbb{N}$ of
de Bruijn variables and every term $t$ of the simply typed lambda calculus with references,
renaming $t$ by $\rho$ and then renaming the result by $\rho'$ gives the same term as renaming $t$
by the composite $\rho' \circ \rho$.
