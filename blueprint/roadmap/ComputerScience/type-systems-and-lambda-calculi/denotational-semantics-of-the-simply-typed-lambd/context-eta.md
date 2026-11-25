# Eta equality inside an STLC context

Let $E$ be a typed one-hole context whose hole
has type $A \Rightarrow B$ in variable context $\Gamma$ and which produces a term of type $C$
in context $\Delta$. For every term $f$ of type $A \Rightarrow B$ in $\Gamma$, the term
$E[\lambda.\,(f^{\uparrow}\,x_0)]$ is model-equal to $E[f]$, where $f^{\uparrow}$ is $f$
weakened by a newest variable of type $A$ and $x_0$ is that variable.
