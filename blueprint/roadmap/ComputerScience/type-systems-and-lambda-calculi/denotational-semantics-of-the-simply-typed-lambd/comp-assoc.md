# Associativity of composition of STLC contexts

Let $E_1$ be a typed one-hole context
whose hole has type $A$ in variable context $\Gamma$ and which produces a term of type $B$ in
context $\Delta$, $E_2$ one with hole of type $B$ in $\Delta$ producing type $C$ in $\Theta$,
and $E_3$ one with hole of type $C$ in $\Theta$ producing type $D$ in $\Xi$. Then
$(E_3 \circ E_2) \circ E_1 = E_3 \circ (E_2 \circ E_1)$.
