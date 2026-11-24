# Type substitution in Fω terms

For a [kind-preserving substitution](../intrinsically-kinded-type-operators-for-pure-f/sub.md)
$\sigma : \Delta \to \mathrm{E}$, the type substitution $t[\sigma] \in \mathrm{Tm}_{\mathrm{E},m}$
of a [term](tm.md) $t \in \mathrm{Tm}_{\Delta,m}$ is defined by $x_i[\sigma] = x_i$, $(\lambda
A.\,b)[\sigma] = \lambda A[\sigma].\,b[\sigma]$, $(f\,a)[\sigma] = f[\sigma]\,a[\sigma]$,
$(\Lambda_\kappa b)[\sigma] = \Lambda_\kappa(b[\sigma^{\uparrow}])$ and $(f\,[A])[\sigma] =
f[\sigma]\,[A[\sigma]]$, using [type
substitution](../intrinsically-kinded-type-operators-for-pure-f/subst.md) on the annotations and the
[lifted substitution](../intrinsically-kinded-type-operators-for-pure-f/lift-sub.md) under type
abstractions.
