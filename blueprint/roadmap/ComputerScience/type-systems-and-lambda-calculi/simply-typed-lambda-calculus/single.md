# Single-variable substitution (simply typed lambda calculus)

Write $A :: \Gamma$ for the
context $\Gamma$ extended by a newest variable of type $A$. Given a term $a$ of type $A$ in
context $\Gamma$, the single-variable substitution for $a$ is the substitution from
$A :: \Gamma$ to $\Gamma$ that sends the newest variable to $a$ and sends the successor of each
variable $x$ of $\Gamma$ to the term consisting of the variable $x$ alone.
