# Closing is invariant under type substitution

For every [kind-preserving substitution](../intrinsically-kinded-type-operators-for-pure-f/sub.md)
$\sigma : \Delta \to \mathrm{E}$, environment $\eta$ of model terms and $t \in
\mathrm{Tm}_{\Delta,m}$, the [closing](close.md) of the [type
substitution](../scoped-pure-f-terms/ty-subst.md) $t[\sigma]$ under $\eta$ equals $t\{\eta\}$.
