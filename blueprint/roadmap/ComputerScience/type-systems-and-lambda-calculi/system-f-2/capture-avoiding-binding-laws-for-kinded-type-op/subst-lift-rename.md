# Lifted substitution commutes with weakening

For a [kind-preserving substitution](../intrinsically-kinded-type-operators-for-pure-f/sub.md)
$\sigma : \Delta \to \mathrm{E}$, a kind $\mu$ and every [type
operator](../intrinsically-kinded-type-operators-for-pure-f/ty.md) $A \in
\mathrm{Ty}^{\kappa}_{\Delta}$, $A\langle\uparrow\rangle[\sigma^{\uparrow}] =
A[\sigma]\langle\uparrow\rangle$, where $\uparrow$ is the successor renaming $\alpha_i \mapsto
\alpha_{i+1}$ (into the context extended by $\mu$) and $\sigma^{\uparrow} : \mu \cdot \Delta \to \mu
\cdot \mathrm{E}$ the [lifted
substitution](../intrinsically-kinded-type-operators-for-pure-f/lift-sub.md).
