# Agreement of substitutions survives lifting under a binder

The erasure of an intrinsically typed term (a term of type $A$ in a context $\Gamma$, a list of simple types) is the raw term obtained by replacing each variable by its de Bruijn index (its position in $\Gamma$, counting from $0$ at the front), keeping applications, and keeping each lambda's parameter type as annotation. A typed substitution $\sigma$ from $\Gamma$ to $\Delta$ agrees with a raw substitution $s$ when the erasure of $\sigma(x)$ is $s(i_x)$ for every variable $x$, with $i_x$ the de Bruijn index of $x$.

If $\sigma$ agrees with $s$, then for every simple type $A$ the lift of $\sigma$ (the substitution from $A :: \Gamma$ to $A :: \Delta$ sending the newest variable to itself and the successor of $x$ to the weakening of $\sigma(x)$) agrees with the raw lift of $s$ (sending $0$ to $\mathrm{var}\,0$ and $n + 1$ to $s(n)$ with every variable index $k$ renamed to $k + 1$, the renaming lifted under binders).
