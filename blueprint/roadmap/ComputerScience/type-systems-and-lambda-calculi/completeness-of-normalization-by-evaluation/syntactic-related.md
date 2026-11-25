# The syntactic logical relation between semantic values and terms

A Kripke semantic value and a term of the same type in a context $\Gamma$ are syntactically
related by recursion on the type. At a base type, a semantic value $n$ (a neutral term) is related
to a term $t$ when the term underlying $n$ is beta-eta convertible to $t$. At an arrow type
$A \Rightarrow B$, a semantic value $f$ is related to a term $t$ when, for every renaming $\rho$
from $\Gamma$ to a context $\Delta$, every semantic value $a$ of type $A$ in $\Delta$ and every
term $s$ of type $A$ in $\Delta$ related to $a$, the value $f(\rho, a)$ is related to the
application of $t$ renamed along $\rho$ to $s$.
