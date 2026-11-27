# Separation-logic while rule

Let $I$ be a heap assertion, $b$ a Boolean expression and
$c$ a heap command. Write $I \wedge b$ for the assertion that holds of a store $s$ and a heap
$h$ when $I(s, h)$ holds and $b$ evaluates to true in $s$, and $I \wedge \neg b$ for the one
that holds when $I(s, h)$ holds and $b$ evaluates to false in $s$. If the triple
$\lbrace I \wedge b \rbrace\ c\ \lbrace I \rbrace$ is valid, then so is the triple
$\lbrace I \rbrace\ \mathtt{while}\ b\ \mathtt{do}\ c\ \lbrace I \wedge \neg b \rbrace$.
