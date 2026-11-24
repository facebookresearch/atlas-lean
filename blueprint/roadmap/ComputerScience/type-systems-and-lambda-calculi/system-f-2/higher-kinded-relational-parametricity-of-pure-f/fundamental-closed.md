# Closed typed Fω terms are related to themselves

Let $\Gamma$ be a term context with no term variables over a kinding context $\Delta$, $t \in
\mathrm{Tm}_{\Delta,0}$ and $A \in \mathrm{Ty}^{\star}_{\Delta}$ with $\Gamma \vdash t : A$
([typing](../pure-f-typing-with-proved-type-beta-conversion/typing.md)). For every environment
$\rho$ of kinded relations for $\Delta$, the
[erasure](../f-closing-instances-in-the-single-existing-term/erase-model.md) of $t$ to the untyped
term model is related to itself by $[\![A]\!]_\rho$ ([relational
interpretation](../higher-kinded-relational-interpretation-of-f-typ/interpret.md)).
