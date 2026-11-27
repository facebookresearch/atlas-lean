# Denotation of an STLC term

Given an interpretation $I$ of the base types, the denotation of
a well-typed term $t$ of type $A$ in context $\Gamma$ in an environment $\eta$ for $\Gamma$ is the
element of the denotation of $A$ defined by recursion on $t$: a variable $x$ denotes $\eta(x)$, an
application $f\,a$ denotes the denotation of $f$ applied to the denotation of $a$ (both in
$\eta$), and an abstraction $\lambda.\,b$ denotes the function sending each value $a$ of
its argument type to the denotation of the body $b$ in $\eta$ extended by $a$ for the newest
variable.
