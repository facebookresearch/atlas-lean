# Hoare rule for annotated while loops in the imperative language with arrays

Let $I$ be a predicate on states, $b$ a Boolean expression and $c$ a statement with $\lbrace s \mapsto I(s) \wedge b(s) \rbrace\ c\ \lbrace I \rbrace$. Then for the loop $\mathtt{while}\ b\ \mathtt{do}\ c$ annotated with this invariant $I$,

$$\lbrace I \rbrace\ \mathtt{while}\ b\ \mathtt{do}\ c\ \lbrace s \mapsto I(s) \wedge \neg b(s) \rbrace.$$
