# Kripke semantic values

For a context $\Gamma$, the semantic values of a simple type in
$\Gamma$ are defined by recursion on the type. At a base type $b$ they are the neutral terms of
type $b$ in $\Gamma$ (variables applied to zero or more normal arguments). At an arrow type
$A \Rightarrow B$ a semantic value is a family that, for every context $\Delta$ and every
renaming from $\Gamma$ to $\Delta$, maps semantic values of type $A$ in $\Delta$ to semantic
values of type $B$ in $\Delta$.

Because a semantic function acts after every renaming into a later context, reification under a
binder needs no untyped weakening operation.
