# Type preservation for Fω weak call-by-value reduction

Let $\Gamma$ be a term context, $t, t' \in \mathrm{Tm}_{\Delta,m}$ and $A \in
\mathrm{Ty}^{\star}_{\Delta}$. If $\Gamma \vdash t : A$
([typing](../pure-f-typing-with-proved-type-beta-conversion/typing.md)) and $t \to t'$ ([weak
call-by-value step](step.md)), then $\Gamma \vdash t' : A$.
