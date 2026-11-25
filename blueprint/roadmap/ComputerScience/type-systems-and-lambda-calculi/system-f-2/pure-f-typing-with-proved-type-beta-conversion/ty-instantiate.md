# Type-binder instantiation preserves Fω typing

Let $\Gamma$ be a term context over $\Delta$, $\kappa$ a kind, $b \in \mathrm{Tm}_{\kappa \cdot
\Delta,m}$ and $C \in \mathrm{Ty}^{\star}_{\kappa \cdot \Delta}$ with $\Gamma^{\uparrow} \vdash b :
C$ ([typing](typing.md), $\Gamma^{\uparrow}$ the weakened context). Then for every $A \in
\mathrm{Ty}^{\kappa}_{\Delta}$, $\Gamma \vdash b[A] : C[A]$, where $b[A]$ is the [type
substitution](../scoped-pure-f-terms/ty-subst.md) of $b$ by the [single
substitution](../intrinsically-kinded-type-operators-for-pure-f/single.md) of $A$ for $\alpha_0$ and
$C[A]$ the [instantiation](../intrinsically-kinded-type-operators-for-pure-f/instantiate.md).
