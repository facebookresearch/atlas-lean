# PCF denotation of instantiation

Let $t$ be a PCF term of type $B$ in the context $\Gamma$
extended by a newest variable of type $A$, let $a$ be a term of type $A$ in context $\Gamma$, and
let $\eta$ be an environment for $\Gamma$. Writing $[\![s]\!]\eta$ for the denotation of a term $s$
at $\eta$, the denotation at $\eta$ of the term obtained from $t$ by substituting $a$ for the newest
variable equals $[\![t]\!](\eta, [\![a]\!]\eta)$, the denotation of $t$ at the extension of $\eta$
that gives the newest variable the value $[\![a]\!]\eta$.
