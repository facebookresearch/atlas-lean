# Substitution commutes with instantiation for intrinsically typed STLC terms

Let $\sigma$
be a substitution from the typing context $\Gamma$ to the typing context $\Delta$, $s$ a term of
type $B$ in the context $\Gamma$ extended by a newest variable of type $A$, and $a$ a term of type
$A$ in context $\Gamma$. Replacing the newest variable of $s$ by $a$ and then applying $\sigma$
gives the same term as applying the lift of $\sigma$ to $s$ and then replacing the newest variable
of the result by the term obtained by applying $\sigma$ to $a$.
