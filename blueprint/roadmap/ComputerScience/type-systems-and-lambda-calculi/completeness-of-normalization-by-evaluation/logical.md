# Logical semantic values

Logical Kripke semantic values are defined by recursion on the type, simultaneously with
[relatedness](related.md). Every semantic value of a base type is logical. A semantic value $f$ of
type $A \Rightarrow B$ in a context $\Gamma$ is logical when it is natural (it sends natural
arguments to natural values and commutes with every renaming into a further context) and, for
every renaming $\rho$ from $\Gamma$ to a context $\Delta$ and all logical semantic values $a$ and
$b$ of type $A$ in $\Delta$ that are related, the values $f(\rho, a)$ and $f(\rho, b)$ are related
at type $B$.
