# Progress for well-typed terms without free term variables

Let $\Gamma$ be a term context with no term variables over $n$ type variables (any $n$), $t \in \mathrm{Tm}_{n,0}$ and $A$ a type with $\Gamma \vdash t : A$ ([typing](../the-five-typing-rules-of-pure-system-f/typing.md)). Then $t$ is a [value](value.md) or $t \to t'$ for some $t'$ ([call-by-value step](step.md)).
