# Fω erasure ignores type substitution

For every [kind-preserving substitution](../intrinsically-kinded-type-operators-for-pure-f/sub.md)
$\sigma : \Delta \to \mathrm{E}$ and every [Fω term](../scoped-pure-f-terms/tm.md) $t \in
\mathrm{Tm}_{\Delta,m}$, $|t[\sigma]| = |t|$, where $t[\sigma]$ is the [type
substitution](../scoped-pure-f-terms/ty-subst.md) and $|\cdot|$ the [erasure](erase-syntax.md) to
System F terms.
