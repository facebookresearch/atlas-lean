# Neutral terms

Neutral terms and normal forms of the simply typed lambda calculus are defined by mutual
induction, indexed by a context $\Gamma$ and a type $A$. Every variable $x$ of type $A$ in
$\Gamma$ is a neutral term of type $A$ in $\Gamma$; and if $f$ is a neutral term of type
$A \Rightarrow B$ and $a$ is a [normal form](nf.md) of type $A$, both in $\Gamma$, then the
application $f\,a$ is a neutral term of type $B$ in $\Gamma$. So a neutral term is a variable
applied to zero or more normal arguments.
