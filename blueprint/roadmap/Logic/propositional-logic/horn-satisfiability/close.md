# Forward-chaining closure

For a CNF formula $\varphi$ and a finite set $T$ of
variables, the closure of $T$ is computed by iterating the forward-chaining step of $\varphi$:
if every variable derived from $T$ already lies in $T$, the closure is $T$; otherwise it is the
closure of the union of $T$ with the derived variables.

The iteration terminates because each step that does not stop adds a variable of $\varphi$.
