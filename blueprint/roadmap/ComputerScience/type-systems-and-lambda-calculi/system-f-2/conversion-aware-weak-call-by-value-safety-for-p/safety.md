# Type safety of Fω weak call-by-value reduction

Let $\Gamma$ be a term context with no term variables over $\Delta$, $t, t' \in
\mathrm{Tm}_{\Delta,0}$ and $A \in \mathrm{Ty}^{\star}_{\Delta}$. If $\Gamma \vdash t : A$
([typing](../pure-f-typing-with-proved-type-beta-conversion/typing.md)) and $t'$ is reachable from
$t$ by finitely many [weak call-by-value steps](step.md), then $t'$ is a [value](value.md) or $t'
\to u$ for some $u$.
