# Term translation commutes with target type substitution

For every map $\varphi$ from $\{0, \dots, n-1\}$ to $\mathrm{Ty}^{\star}_{\Delta}$, every
[kind-preserving substitution](../intrinsically-kinded-type-operators-for-pure-f/sub.md) $\sigma :
\Delta \to \mathrm{E}$ and every System F term $t \in \mathrm{Tm}_{n,m}$,
$\mathcal{T}_\varphi(t)[\sigma] = \mathcal{T}_{\varphi'}(t)$ with $\varphi'(i) = \varphi(i)[\sigma]$
([term translation](from-system-f-2.md), [type substitution in Fω
terms](../scoped-pure-f-terms/ty-subst.md)).
