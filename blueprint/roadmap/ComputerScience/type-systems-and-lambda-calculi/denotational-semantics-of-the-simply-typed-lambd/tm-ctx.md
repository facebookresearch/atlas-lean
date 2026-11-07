# Typed one-hole contexts

Fix simple types over a type of base types. A one-hole context
whose hole has type $A$ in variable context $\Gamma$, and which produces a term of type $B$ in
variable context $\Delta$, is built by four rules. The hole itself is such a context, with
$\Delta = \Gamma$ and $B = A$. If $C$ produces type $S \Rightarrow T$ in $\Delta$ and $a$ is a term
of type $S$ in $\Delta$, then the application $C\,a$ produces type $T$ in $\Delta$. If $f$ is a
term of type $S \Rightarrow T$ in $\Delta$ and $C$ produces type $S$ in $\Delta$, then the
application $f\,C$ produces type $T$ in $\Delta$. If $C$ produces type $T$ in the context
$S :: \Delta$ obtained from $\Delta$ by adding a new leading variable of type $S$, then the
abstraction $\lambda C$ produces type $S \Rightarrow T$ in $\Delta$. In every rule the hole keeps
type $A$ in context $\Gamma$.
