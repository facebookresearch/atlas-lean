# The let rule under a type substitution

Let $\Gamma$ be a typing context, $s$ a type
substitution, $x$ a variable name, $e_1, e_2$ expressions and $\tau_1, \tau_2$ monotypes, and
write $s\Gamma$ for the context obtained by applying $s$ to every type scheme of $\Gamma$.
Suppose $e_1$ has type $\tau_1$ in $\Gamma$, and $e_2$ has type $\tau_2$ in the context
obtained from $s\Gamma$ by binding $x$, in front, to the type scheme that results from
applying $s$ to the generalization of $\tau_1$ in $\Gamma$. Then
$\mathtt{let}\ x = e_1\ \mathtt{in}\ e_2$ has type $\tau_2$ in $s\Gamma$.
