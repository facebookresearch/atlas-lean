# Fundamental lemma of formal approximation

Let $t$ be a PCF term of type $A$ in a context
$\Gamma$, let $\eta$ be a semantic environment for $\Gamma$, and let $\sigma$ assign to each
variable of $\Gamma$ a closed term of the same type. Suppose that for every variable $x$ of
$\Gamma$, of type $B$ say, the value of $x$ in $\eta$ formally approximates the closed term
$\sigma(x)$ at type $B$. Then the denotation of $t$ in $\eta$ formally approximates, at type $A$,
the closed term $\sigma(t)$ obtained by simultaneously substituting $\sigma(x)$ for each
variable $x$ in $t$.
