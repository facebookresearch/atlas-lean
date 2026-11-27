# Composition of substitutions for intrinsically typed STLC terms

Let $\sigma$ be a
substitution from the typing context $\Gamma$ to the typing context $\Delta$, $\tau$ a
substitution from $\Delta$ to the typing context $\Xi$, and $t$ a term of type $A$ in context
$\Gamma$. Applying $\sigma$ to $t$ and then applying $\tau$ gives the same term as applying to $t$
the composite substitution, which sends each variable $x$ of $\Gamma$ to the result of applying
$\tau$ to $\sigma(x)$.
