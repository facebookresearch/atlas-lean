# Local transition relation of the LTL tableau

The local step relation of the LTL tableau of $\varphi$. A tableau state assigns a truth value to
each occurrence of a subformula of $\varphi$. A step from $s$ to $t$ on a letter $x$ requires that
$s$ gives each atom the value of the valuation at $x$, gives $\top$ the value true, respects
negation and conjunction, gives $\bigcirc\psi$ the value of $\psi$ in $t$, and gives
$\psi\, \mathcal{U}\, \chi$ the value of $\chi \lor (\psi \land \text{the until in } t)$. The letter
labels the source state $s$.
