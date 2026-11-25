# CPS translation at a base type

Fix an answer type $R$ and an interpretation $I$ of the
base types; write $D(A)$ for the set interpreting a type $A$, $\overline{\Gamma}$ and
$\overline{t}$ for the call-by-value CPS translations of contexts and terms, and $[t]_\eta$ for
the denotation of a term $t$ in an environment $\eta$. Let $t$ be a term of base type $b$ in
context $\Gamma$, and let $\eta$ and $\eta'$ be related environments for $\Gamma$ and
$\overline{\Gamma}$. Then $[\overline{t}]_{\eta'}(k) = k([t]_\eta)$ for every continuation
$k \colon I(b) \to D(R)$.
