# Plugging a term into a PCF context

Let $C$ be a one-hole context that turns terms of type
$A$ in context $\Gamma$ into terms of type $B$ in context $\Delta$, and $t$ a term of type $A$ in
context $\Gamma$. The term $C[t]$ of type $B$ in context $\Delta$ is defined by recursion on $C$:
if $C$ is the hole, $C[t] = t$; if $C$ applies a term former (abstraction, application on either
side, successor, predecessor, the zero test at any of its three arguments, or the fixed point) to
a subcontext $C'$ and fixed terms, $C[t]$ applies the same former to $C'[t]$ and the same terms;
and if $C$ is a subcontext $C'$ carried along a renaming $\rho$, then $C[t]$ is $C'[t]$ renamed
by $\rho$.
