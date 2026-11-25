# Type translation preserves the relational interpretation

For every map $\varphi$ from $\{0, \dots, n-1\}$ to $\mathrm{Ty}^{\star}_{\Delta}$, every
environment $\rho$ of kinded relations for $\Delta$ and every System F type $A \in \mathrm{Ty}_n$,
the [Fω relational interpretation](../higher-kinded-relational-interpretation-of-f-typ/interpret.md)
of the [translation](../the-star-forall-system-f-fragment-inside-pure-f/from-system-f.md) satisfies
$[\![\mathcal{T}_\varphi(A)]\!]_\rho = [\![A]\!]_{\rho'}$, the [System F relational
interpretation](../../system-f/impredicative-binary-interpretation-of-system-f/interpret.md) under
$\rho'(i) = [\![\varphi(i)]\!]_\rho$.
