# Depth of a formula

The depth $d(\varphi)$ of a first-order formula $\varphi$ is the
nesting height of its implications and universal quantifiers: $\bot$, equations and relation
atoms have depth $0$, the implication $\varphi \to \psi$ has depth
$\max(d(\varphi), d(\psi)) + 1$, and $\forall \varphi$ has depth $d(\varphi) + 1$.
