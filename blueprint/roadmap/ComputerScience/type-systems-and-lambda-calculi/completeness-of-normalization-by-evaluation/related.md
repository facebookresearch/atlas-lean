# Logical relatedness of semantic values

Relatedness of Kripke semantic values is defined by recursion on the type, simultaneously with
[logical semantic values](logical.md). Two semantic values of a base type are related when they
are equal neutral terms. Two semantic values $f$ and $g$ of type $A \Rightarrow B$ in a context
$\Gamma$ are related when, for every renaming $\rho$ from $\Gamma$ to a context $\Delta$ and all
logical semantic values $a$ and $b$ of type $A$ in $\Delta$ that are related, the values
$f(\rho, a)$ and $g(\rho, b)$ are related at type $B$. This is observational equality of semantic
values.
