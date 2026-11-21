# Term translation commutes with type-binder instantiation

For every map $\varphi$ from $\{0, \dots, n-1\}$ to $\mathrm{Ty}^{\star}_{\Delta}$, every System F
term $b \in \mathrm{Tm}_{n+1,m}$ and type $A \in \mathrm{Ty}_n$, $\mathcal{T}_\varphi(b[A]) =
\mathcal{T}_{\varphi^{\uparrow}}(b)[\mathcal{T}_\varphi(A)]$, where on the left $b[A]$ is the System
F type substitution of $A$ for $\alpha_0$ and on the right the Fω [type
substitution](../scoped-pure-f-terms/ty-subst.md) by the [single
substitution](../intrinsically-kinded-type-operators-for-pure-f/single.md) ([term
translation](from-system-f-2.md)).
