# Big-step semantics of the closure-conversion target

Evaluation $\rho \vdash e \Downarrow v$
of a target term $e$ to a target value $v$ in an environment $\rho$ (a list of values, where
variable $n$ refers to the entry of $\rho$ at index $n$, counting from $0$) is the least relation
closed under the following rules. A variable $n$ evaluates to the entry of $\rho$ at index $n$,
when that entry exists. Code evaluates to itself: $\rho \vdash \mathsf{code}\,b \Downarrow
\mathsf{code}\,b$. If $\rho \vdash f \Downarrow \mathsf{code}\,b$, $\rho \vdash a \Downarrow v$ and
$[v] \vdash b \Downarrow w$, then $\rho \vdash f\,a \Downarrow w$; so a code body runs in the
one-element environment $[v]$ and never sees $\rho$. The unit term evaluates to the unit value.
If $\rho \vdash a \Downarrow v$ and $\rho \vdash b \Downarrow w$, then
$\rho \vdash (a, b) \Downarrow (v, w)$. If $\rho \vdash e \Downarrow (v, w)$, then
$\rho \vdash \mathsf{fst}\,e \Downarrow v$ and $\rho \vdash \mathsf{snd}\,e \Downarrow w$. If
$\rho \vdash e \Downarrow v$ and $v :: \rho \vdash b \Downarrow w$, where $v :: \rho$ is $\rho$
with $v$ added at index $0$, then $\rho \vdash \mathsf{let}\ e\ \mathsf{in}\ b \Downarrow w$.
