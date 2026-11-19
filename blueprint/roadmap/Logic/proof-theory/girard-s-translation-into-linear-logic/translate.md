# Girard's translation

Given a map $f$ from propositional atoms to CLL propositions, the
translation $A \mapsto A^\circ$ of propositional formulas into CLL is defined by recursion:
$a^\circ = f(a)$ for an atom $a$, $(A \wedge B)^\circ = A^\circ \mathbin{\&} B^\circ$,
$(A \vee B)^\circ = {!A^\circ} \oplus {!B^\circ}$, and $(A \to B)^\circ$ is the multiplicative
disjunction (par) of $?\big((A^\circ)^\perp\big)$ and $B^\circ$, that is, the linear implication
${!A^\circ} \multimap B^\circ$.
