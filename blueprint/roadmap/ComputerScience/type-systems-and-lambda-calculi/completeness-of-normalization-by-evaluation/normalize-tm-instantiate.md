# The normalized term of a beta instantiation

Let $b$ be a term of type $B$ in the context $\Gamma$ extended by $A$ and let $a$ be a term of type
$A$ in $\Gamma$. The normalized term of $b[a]$, the term $b$ with its new variable instantiated by
$a$, is the term underlying the reification at type $B$ of the evaluation of $b$ in the
environment that sends the new variable to the evaluation of $a$ in the identity semantic
environment of $\Gamma$ and each other variable $x$ to the reflection of $x$.
