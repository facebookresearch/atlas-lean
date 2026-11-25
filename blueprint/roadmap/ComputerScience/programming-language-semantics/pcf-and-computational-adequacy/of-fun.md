# Environment from a family of values

Let $\Gamma$ be a context, that is, a list of PCF
types, and suppose that for every type $A$ and every variable $x$ of type $A$ in $\Gamma$ we are
given a value $f(x)$ in the domain denoted by $A$. The environment built from $f$ is the
environment for $\Gamma$ defined by recursion on $\Gamma$: for the empty context it is the unique
element of the one-point domain, and for the context obtained from $\Gamma'$ by adding a newest
variable of type $B$ it is the pair of the environment built from $f$ on the older variables of
$\Gamma'$ and the value of $f$ at the newest variable. So its entry at every variable $x$ is
$f(x)$.
