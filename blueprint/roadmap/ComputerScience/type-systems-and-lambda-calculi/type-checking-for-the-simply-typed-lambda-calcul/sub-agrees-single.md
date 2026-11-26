# Agreement of the single-variable substitutions

The erasure of an intrinsically typed term (a term of type $A$ in a context $\Gamma$, a list of simple types) is the raw term obtained by replacing each variable by its de Bruijn index (its position in $\Gamma$, counting from $0$ at the front), keeping applications, and keeping each lambda's parameter type as annotation. A typed substitution $\sigma$ from $\Gamma$ to $\Delta$ agrees with a raw substitution $s$ when the erasure of $\sigma(x)$ is $s(i_x)$ for every variable $x$, with $i_x$ the de Bruijn index of $x$.

For every term $a$ of type $A$ in $\Gamma$, the typed single-variable substitution for $a$ (from $A :: \Gamma$ to $\Gamma$, sending the newest variable to $a$ and the successor of $x$ to the variable $x$) agrees with the raw single-variable substitution for the erasure of $a$ (sending $0$ to the erasure of $a$ and $n + 1$ to $\mathrm{var}\,n$).
