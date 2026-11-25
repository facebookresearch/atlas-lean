# Substituting by an extended substitution, via lifting

Let $\sigma$ be a substitution from
the typing context $\Gamma$ to the typing context $\Delta$, $s$ a term of type $B$ in the context
$\Gamma$ extended by a newest variable of type $A$, and $a$ a term of type $A$ in context
$\Delta$. Applying to $s$ the extension of $\sigma$ that sends the newest variable to $a$ gives the
same term as applying the lift of $\sigma$ to $s$ and then replacing the newest variable of the
result by $a$.
