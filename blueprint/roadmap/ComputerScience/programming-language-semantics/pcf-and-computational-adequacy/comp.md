# Composition of PCF contexts

Let $C$ be a one-hole context whose hole takes terms of type
$B$ in typing context $\Delta$ and which produces terms of type $B'$ in typing context $\Theta$,
and let $D$ be a one-hole context whose hole takes terms of type $A$ in typing context $\Gamma$
and which produces terms of type $B$ in typing context $\Delta$. The composite $C \circ D$ is the
context obtained from $C$ by replacing its hole by $D$; its hole takes terms of type $A$ in
typing context $\Gamma$, and it produces terms of type $B'$ in typing context $\Theta$.
