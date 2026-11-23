# Term translation preserves System F typing

Let $\Gamma$ be a System F term context, $t \in \mathrm{Tm}_{n,m}$ and $A \in \mathrm{Ty}_n$ with
$\Gamma \vdash t : A$ ([System F
typing](../../system-f/the-five-typing-rules-of-pure-system-f/typing.md)). Then for every map
$\varphi$ from $\{0, \dots, n-1\}$ to $\mathrm{Ty}^{\star}_{\Delta}$, $\mathcal{T}_\varphi(\Gamma)
\vdash \mathcal{T}_\varphi(t) : \mathcal{T}_\varphi(A)$ in pure Fω
([typing](../pure-f-typing-with-proved-type-beta-conversion/typing.md)), where
$\mathcal{T}_\varphi(\Gamma)(i) = \mathcal{T}_\varphi(\Gamma(i))$.
