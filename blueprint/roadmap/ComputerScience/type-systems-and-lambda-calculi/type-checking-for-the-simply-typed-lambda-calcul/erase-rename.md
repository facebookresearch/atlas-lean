# Erasure commutes with renaming

Let $\rho$ be a typed renaming from context $\Gamma$
to $\Delta$ and let $r : \mathbb{N} \to \mathbb{N}$ be a numerical renaming that agrees with
$\rho$. Then for every intrinsically typed term $t$ of type $A$ in context $\Gamma$, the
erasure of the renamed term $\rho(t)$ equals the raw renaming by $r$ (lifted at every binder)
of the erasure of $t$.
