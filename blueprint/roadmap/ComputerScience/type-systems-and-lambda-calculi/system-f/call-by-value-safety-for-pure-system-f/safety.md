# Type safety for closed well-typed terms

Let $\Gamma$ be a term context with no term variables over $n$ type variables, $t, t' \in \mathrm{Tm}_{n,0}$ and $A$ a type. If $\Gamma \vdash t : A$ ([typing](../the-five-typing-rules-of-pure-system-f/typing.md)) and $t \to^* t'$ ([multi-step evaluation](steps.md)), then $t'$ is a [value](value.md) or $t' \to t''$ for some $t''$: no term reachable from a well-typed term without free term variables is stuck.
