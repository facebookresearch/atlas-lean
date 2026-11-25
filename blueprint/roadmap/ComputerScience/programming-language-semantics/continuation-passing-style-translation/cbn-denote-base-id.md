# Running the call-by-name CPS translation with the identity continuation

Fix an
interpretation of the base types. Let $t$ be a term of a base type $b$ in a context $\Gamma$, take
the answer type to be $b$, let $\eta$ be an environment for $\Gamma$, and let $\eta'$ be an
environment for the translated context related to $\eta$. Then the denotation in $\eta'$ of the
call-by-name CPS translation $\overline{t}$ of $t$, applied to the identity function on the values
of type $b$, equals the denotation of $t$ in $\eta$.
