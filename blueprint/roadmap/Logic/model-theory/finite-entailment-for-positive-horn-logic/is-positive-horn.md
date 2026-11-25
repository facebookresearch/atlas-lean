# Equality-free positive Horn formulas

Let $L$ be a first-order language. The equality-free positive Horn formulas of $L$ (with free variables from a set $\alpha$ and finitely many bound-variable slots) form the smallest class of formulas that

- contains every relational atom $R(t_1, \dots, t_l)$, for a relation symbol $R$ of arity $l$ and terms $t_1, \dots, t_l$;
- is closed under conjunction: if $\varphi$ and $\psi$ are in the class, so is $\varphi \wedge \psi$;
- is closed under universal and existential quantification: if $\varphi$ is in the class, so are $\forall x\, \varphi$ and $\exists x\, \varphi$.

No equality atoms, $\bot$, negation, disjunction or implication occur except as the standard encodings of $\wedge$ and $\exists$.
