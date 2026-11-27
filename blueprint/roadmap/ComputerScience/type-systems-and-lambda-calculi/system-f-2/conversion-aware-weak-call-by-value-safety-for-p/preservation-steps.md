# Type preservation along multistep Fω reduction

Let $\Gamma$ be a term context, $t, t' \in \mathrm{Tm}_{\Delta,m}$ and $A \in
\mathrm{Ty}^{\star}_{\Delta}$. If $\Gamma \vdash t : A$
([typing](../pure-f-typing-with-proved-type-beta-conversion/typing.md)) and $t'$ is reachable from
$t$ by finitely many (possibly zero) [weak call-by-value steps](step.md), then $\Gamma \vdash t' :
A$.
