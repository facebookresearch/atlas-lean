# Instantiating a weakened type operator leaves it unchanged

For every [type operator](../intrinsically-kinded-type-operators-for-pure-f/ty.md) $A \in
\mathrm{Ty}^{\kappa}_{\Delta}$ and $B \in \mathrm{Ty}^{\mu}_{\Delta}$, $A\langle\uparrow\rangle[B] =
A$, where $\uparrow : \Delta \to \mu \cdot \Delta$ is the successor renaming $\alpha_i \mapsto
\alpha_{i+1}$ and $[B]$ is the
[instantiation](../intrinsically-kinded-type-operators-for-pure-f/instantiate.md) of $\alpha_0$ by
$B$.
