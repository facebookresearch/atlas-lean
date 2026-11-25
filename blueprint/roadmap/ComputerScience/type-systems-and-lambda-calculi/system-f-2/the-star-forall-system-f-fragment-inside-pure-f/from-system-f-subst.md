# Term translation commutes with term substitution

For every map $\varphi$ from $\{0, \dots, n-1\}$ to $\mathrm{Ty}^{\star}_{\Delta}$, every System F
term substitution $\sigma$ from $m$ to $k$ term variables and every System F term $t \in
\mathrm{Tm}_{n,m}$, $\mathcal{T}_\varphi(t[\sigma]) = \mathcal{T}_\varphi(t)[\sigma']$ with
$\sigma'(i) = \mathcal{T}_\varphi(\sigma(i))$ ([term translation](from-system-f-2.md), [Fω term
substitution](../scoped-pure-f-terms/subst.md)).
