# Beta is sound for the denotational semantics

For every interpretation $I$ of the base
types, every term $t$ of type $B$ in the context $\Gamma$ extended by a newest variable of type
$A$, and every term $a$ of type $A$ in $\Gamma$, the redex $(\lambda.\,t)\,a$ is semantically
equal in $I$ (has the same denotation in every environment) to the instantiation $t[a]$, which
replaces the newest free variable of $t$ by $a$.

The argument $a$ need not be a value.
