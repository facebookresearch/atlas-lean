# Declarative typing of raw terms

For a context $\Gamma$ (a list of simple types), a
raw term $t$ and a type $A$, the judgment $\Gamma \vdash t : A$ is the least relation closed
under three rules. A variable with de Bruijn index $n$ has type $A$ in $\Gamma$ whenever looking
up $n$ in $\Gamma$ succeeds with the type $A$ and some intrinsic variable of type $A$. If
$\Gamma \vdash f : A \Rightarrow B$ and $\Gamma \vdash a : A$, then the application $f\,a$ has
type $B$ in $\Gamma$. If $A :: \Gamma \vdash b : B$, where $A :: \Gamma$ is $\Gamma$ with $A$
added at the front, then the abstraction $\lambda{:}A.\,b$ with parameter type $A$ has type
$A \Rightarrow B$ in $\Gamma$.
