# Relational interpretation of embedded types

For every System F type $A \in \mathrm{Ty}_n$ and every assignment $\rho$ of [β-invariant
relations](../../system-f/binary-beta-invariant-relations/rel.md) to the type variables of the
kinding context $\star^n$, the [Fω relational
interpretation](../higher-kinded-relational-interpretation-of-f-typ/interpret.md) of the
[embedding](../the-star-forall-system-f-fragment-inside-pure-f/embed.md) satisfies
$[\![\mathcal{E}(A)]\!]_\rho = [\![A]\!]_{\rho'}$, the [System F relational
interpretation](../../system-f/impredicative-binary-interpretation-of-system-f/interpret.md) under
$\rho'(i) = \rho(\alpha_i)$.
