# Denotational correctness of the CPS translation (Meyer–Wand)

Fix an answer type $R$
and an interpretation $I$ of the base types; write $D(A)$ for the set interpreting a type $A$,
$\overline{A}$, $\overline{\Gamma}$ and $\overline{t}$ for the call-by-value CPS translations of
types, contexts and terms, and $[t]_\eta$ for the denotation of a term $t$ in an environment
$\eta$. Let $t$ be a term of type $A$ in context $\Gamma$, and let $\eta$ and $\eta'$ be related
environments for $\Gamma$ and $\overline{\Gamma}$. Then there is a value $v' \in D(\overline{A})$,
related to $[t]_\eta$ by the CPS logical relation at $A$, such that $[\overline{t}]_{\eta'}(k) =
k(v')$ for every continuation $k \colon D(\overline{A}) \to D(R)$.
