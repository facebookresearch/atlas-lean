# Lifted substitution commutes with weakening for intrinsically typed STLC terms

Let
$\sigma$ be a substitution from the typing context $\Gamma$ to the typing context $\Delta$, $t$ a
term of type $A$ in context $\Gamma$, and $B$ a type. Weakening $t$ by a new newest variable of
type $B$ and then applying the lift of $\sigma$ under that variable gives the same term as
applying $\sigma$ to $t$ and then weakening by a new newest variable of type $B$.
