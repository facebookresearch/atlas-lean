# Type translation commutes with target substitution

For every map $\varphi$ from $\{0, \dots, n-1\}$ to $\mathrm{Ty}^{\star}_{\Delta}$, every
[kind-preserving substitution](../intrinsically-kinded-type-operators-for-pure-f/sub.md) $\sigma :
\Delta \to \mathrm{E}$ and every System F type $A \in \mathrm{Ty}_n$,
$\mathcal{T}_\varphi(A)[\sigma] = \mathcal{T}_{\varphi'}(A)$ with $\varphi'(i) = \varphi(i)[\sigma]$
([translation](from-system-f.md)).
