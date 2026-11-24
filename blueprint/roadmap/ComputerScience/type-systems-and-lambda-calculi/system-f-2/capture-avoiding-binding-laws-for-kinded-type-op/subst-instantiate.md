# Substitution commutes with type-binder instantiation

For a [kind-preserving substitution](../intrinsically-kinded-type-operators-for-pure-f/sub.md)
$\sigma : \Delta \to \mathrm{E}$, $B \in \mathrm{Ty}^{\kappa}_{\mu \cdot \Delta}$ and $A \in
\mathrm{Ty}^{\mu}_{\Delta}$, $(B[A])[\sigma] = (B[\sigma^{\uparrow}])[A[\sigma]]$, with the [lifted
substitution](../intrinsically-kinded-type-operators-for-pure-f/lift-sub.md) $\sigma^{\uparrow}$ and
[instantiation](../intrinsically-kinded-type-operators-for-pure-f/instantiate.md).
