# The de Bruijn index of a typed variable is below the context length

For every context $\Gamma$ (a list of simple types), simple type $A$ and variable $x$ of type $A$ in $\Gamma$, the de Bruijn index of $x$ (the newest variable has index $0$, and the successor of $x$ has index one more than $x$) is less than the length of $\Gamma$.
