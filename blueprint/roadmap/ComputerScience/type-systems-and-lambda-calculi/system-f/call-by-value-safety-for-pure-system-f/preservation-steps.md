# Type preservation along evaluation sequences

Let $\Gamma$ be any term context, $t$, $t'$ terms and $A$ a type. If $\Gamma \vdash t : A$ ([typing](../the-five-typing-rules-of-pure-system-f/typing.md)) and $t \to^* t'$ ([multi-step evaluation](steps.md)), then $\Gamma \vdash t' : A$.
