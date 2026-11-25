# Pointwise convertible substitutions give convertible results

Let $\sigma, \tau : \Delta \to \mathrm{E}$ be [kind-preserving
substitutions](../intrinsically-kinded-type-operators-for-pure-f/sub.md) with $\sigma(\alpha_i)
\equiv_\beta \tau(\alpha_i)$ for every type variable $\alpha_i$ of $\Delta$ ([type
β-conversion](conv.md)). Then $A[\sigma] \equiv_\beta A[\tau]$ for every [type
operator](../intrinsically-kinded-type-operators-for-pure-f/ty.md) $A \in
\mathrm{Ty}^{\kappa}_{\Delta}$.
