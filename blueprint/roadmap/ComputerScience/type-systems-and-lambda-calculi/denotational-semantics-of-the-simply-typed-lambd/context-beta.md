# Beta equality inside an STLC context

Let $E$ be a typed one-hole context whose hole
has type $B$ in variable context $\Gamma$ and which produces a term of type $C$ in context
$\Delta$. For every term $b$ of type $B$ in $\Gamma$ extended by a newest variable of type
$A$, and every term $a$ of type $A$ in $\Gamma$, the term $E[(\lambda.\,b)\,a]$ is
model-equal to $E[b[a]]$, where $b[a]$ is the result of substituting $a$ for the newest
variable of $b$.
