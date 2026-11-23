# Instantiation after substitution under a binder

Let $\sigma$ be a substitution from a
context $\Gamma$ to a context $\Delta$, let $b$ be a term of type $B$ in $\Gamma$ extended by a
newest variable of type $A$, and let $a$ be a term of type $A$ in $\Delta$. Applying the lift of
$\sigma$ to $b$ and then instantiating the newest variable with $a$ gives the same term as
applying to $b$ the extension of $\sigma$ by $a$, which sends the newest variable to $a$ and
every older variable $x$ to $\sigma(x)$.
