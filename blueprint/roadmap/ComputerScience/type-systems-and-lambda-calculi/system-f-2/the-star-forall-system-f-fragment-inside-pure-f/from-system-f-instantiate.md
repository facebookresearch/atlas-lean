# Type translation commutes with type-binder instantiation

For every map $\varphi$ from $\{0, \dots, n-1\}$ to $\mathrm{Ty}^{\star}_{\Delta}$, $B \in
\mathrm{Ty}_{n+1}$ and $A \in \mathrm{Ty}_n$, $\mathcal{T}_\varphi(B[A]) =
\mathcal{T}_{\varphi^{\uparrow}}(B)[\mathcal{T}_\varphi(A)]$, with [System F
instantiation](../../system-f/scoped-pure-system-f/instantiate.md) on the left and [Fω
instantiation](../intrinsically-kinded-type-operators-for-pure-f/instantiate.md) on the right
([translation](from-system-f.md)).
