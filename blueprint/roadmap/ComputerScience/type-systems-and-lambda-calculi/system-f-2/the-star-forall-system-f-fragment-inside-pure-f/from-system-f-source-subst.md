# Type translation of a source substitution

For every map $\varphi$ from $\{0, \dots, k-1\}$ to $\mathrm{Ty}^{\star}_{\Delta}$, every System F
type substitution $\sigma$ from $n$ to $k$ type variables and every $A \in \mathrm{Ty}_n$,
$\mathcal{T}_\varphi(A[\sigma]) = \mathcal{T}_{\varphi'}(A)$ with $\varphi'(i) =
\mathcal{T}_\varphi(\sigma(i))$ ([translation](from-system-f.md), [System F
substitution](../../system-f/scoped-pure-system-f/subst.md)).
