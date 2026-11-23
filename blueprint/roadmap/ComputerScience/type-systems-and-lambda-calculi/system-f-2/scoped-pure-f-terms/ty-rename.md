# Type-variable renaming in Fω terms

For a [kind-preserving renaming](../intrinsically-kinded-type-operators-for-pure-f/kren.md) $\rho :
\Delta \to \mathrm{E}$, the type renaming of a [term](tm.md) $t \in \mathrm{Tm}_{\Delta,m}$ is its
[type substitution](ty-subst.md) by the substitution sending each type variable $\alpha_i$ to the
variable $\rho(\alpha_i)$.
