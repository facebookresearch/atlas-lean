# Canonical forms of function-typed values

Let $\Gamma$ be a term context, $t$ a term and $A$, $B$ types. If $\Gamma \vdash t : A \to B$ ([typing](../the-five-typing-rules-of-pure-system-f/typing.md)) and $t$ is a [value](value.md), then $t = \lambda A.\,b$ for some body $b$: an abstraction with the declared argument type $A$.
