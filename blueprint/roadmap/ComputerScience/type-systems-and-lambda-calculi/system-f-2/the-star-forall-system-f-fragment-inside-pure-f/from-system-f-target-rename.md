# Type translation commutes with target renaming

For every map $\varphi$ from $\{0, \dots, n-1\}$ to $\mathrm{Ty}^{\star}_{\Delta}$, every
[kind-preserving renaming](../intrinsically-kinded-type-operators-for-pure-f/kren.md) $\rho : \Delta
\to \mathrm{E}$ and every System F type $A \in \mathrm{Ty}_n$,
$\mathcal{T}_\varphi(A)\langle\rho\rangle = \mathcal{T}_{\varphi'}(A)$ with $\varphi'(i) =
\varphi(i)\langle\rho\rangle$ ([translation](from-system-f.md)).
