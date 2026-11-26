# Hoare rule for conditionals in the imperative language with arrays

For all predicates $P$, $Q$ on states, Boolean expressions $b$ and statements $c_1$, $c_2$: if $\lbrace s \mapsto P(s) \wedge b(s) \rbrace\ c_1\ \lbrace Q \rbrace$ and $\lbrace s \mapsto P(s) \wedge \neg b(s) \rbrace\ c_2\ \lbrace Q \rbrace$, then $\lbrace P \rbrace\ \mathtt{if}\ b\ \mathtt{then}\ c_1\ \mathtt{else}\ c_2\ \lbrace Q \rbrace$.
