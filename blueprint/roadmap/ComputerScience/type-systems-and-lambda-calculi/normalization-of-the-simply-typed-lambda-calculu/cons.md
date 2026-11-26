# Extending a reducible substitution by a reducible term keeps it reducible

Let $\sigma$
be a substitution that sends each variable of a context $\Gamma$ to a closed term of the same
type, and let $a$ be a closed term of type $A$. If $\sigma$ and $a$ are reducible, then so is
the substitution on the context $A, \Gamma$ that sends the newest variable to $a$ and each
older variable $x$ to $\sigma(x)$.
