# Plugging into a composite STLC context

Let $E_2$ be a typed one-hole context whose
hole has type $B$ in variable context $\Delta$ and which produces a term of type $C$ in
context $\Theta$, and let $E_1$ be one whose hole has type $A$ in context $\Gamma$ and which
produces a term of type $B$ in $\Delta$. Then for every term $t$ of type $A$ in $\Gamma$,
$(E_2 \circ E_1)[t] = E_2[E_1[t]]$.
