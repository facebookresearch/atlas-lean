# Beta-normal, eta-long normal forms

Normal forms and [neutral terms](ne.md) of the simply typed lambda calculus are defined by mutual
induction, indexed by a context $\Gamma$ and a type. A neutral term of a base type $b$ in
$\Gamma$ is a normal form of type $b$ in $\Gamma$; and if $t$ is a normal form of type $B$ in the
context $\Gamma$ extended by $A$, then $\lambda t$ is a normal form of type $A \Rightarrow B$ in
$\Gamma$. So at an arrow type every normal form is a $\lambda$-abstraction, and at a base type it
is neutral.
