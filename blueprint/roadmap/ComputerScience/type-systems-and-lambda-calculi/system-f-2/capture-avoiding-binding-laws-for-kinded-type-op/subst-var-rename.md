# Renaming as substitution by variables

For a [kind-preserving renaming](../intrinsically-kinded-type-operators-for-pure-f/kren.md) $\rho :
\Delta \to \mathrm{E}$ and every [type
operator](../intrinsically-kinded-type-operators-for-pure-f/ty.md) $A \in
\mathrm{Ty}^{\kappa}_{\Delta}$, substituting each variable $\alpha_i$ by the variable
$\rho(\alpha_i)$ gives the renaming: $A[\alpha_i \mapsto \rho(\alpha_i)] = A\langle\rho\rangle$.
