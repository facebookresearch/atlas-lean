# Agreement of a typed substitution with a raw substitution

The erasure of an intrinsically typed term (a term of type $A$ in a context $\Gamma$, a list of simple types) is the raw term obtained by replacing each variable by its de Bruijn index (its position in $\Gamma$, counting from $0$ at the front), keeping applications, and keeping each lambda's parameter type as annotation.

For contexts $\Gamma$ and $\Delta$, a typed simultaneous substitution $\sigma$ from $\Gamma$ to $\Delta$ (a term $\sigma(x)$ of type $A$ in $\Delta$ for each variable $x$ of type $A$ in $\Gamma$) agrees with a raw substitution $s : \mathbb{N} \to$ raw terms when, for every simple type $A$ and every variable $x$ of type $A$ in $\Gamma$, the erasure of $\sigma(x)$ equals $s(i_x)$, where $i_x$ is the de Bruijn index of $x$ (the newest variable has index $0$, and the successor of $x$ has index $i_x + 1$).
