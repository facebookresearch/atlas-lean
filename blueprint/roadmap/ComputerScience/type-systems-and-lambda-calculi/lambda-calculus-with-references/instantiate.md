# Substitution lemma for the lambda calculus with references

Let $\Gamma$ be a variable
context and $S$ a store typing. If a term $t$ has type $T$ under $S$ and the context that extends
$\Gamma$ by a new innermost variable (index $0$) of type $A$, and a term $s$ has type $A$ under
$\Gamma$ and $S$, then substituting $s$ for variable $0$ in $t$ (and lowering every other variable
by one) gives a term of type $T$ under $\Gamma$ and $S$.

This is TAPL Lemma 13.5.4 in de Bruijn form.
