# Substitution after renaming of type operators

For a [kind-preserving renaming](../intrinsically-kinded-type-operators-for-pure-f/kren.md) $\rho :
\Delta \to \mathrm{E}$, a [kind-preserving
substitution](../intrinsically-kinded-type-operators-for-pure-f/sub.md) $\sigma : \mathrm{E} \to
\mathrm{Z}$ and every [type operator](../intrinsically-kinded-type-operators-for-pure-f/ty.md) $A
\in \mathrm{Ty}^{\kappa}_{\Delta}$, $A\langle\rho\rangle[\sigma] = A[\sigma \circ \rho]$, where
$\sigma \circ \rho$ sends $\alpha_i$ to $\sigma(\rho(\alpha_i))$.
