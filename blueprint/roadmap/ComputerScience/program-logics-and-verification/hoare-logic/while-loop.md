# Invariant rule for while loops

Let $I$ be an assertion, $b$ a Boolean expression and
$c$ a command. Write $I \wedge b$ for the assertion that $I$ holds and $b$ evaluates to true,
and $I \wedge \neg b$ for the assertion that $I$ holds and $b$ evaluates to false. If the
partial-correctness Hoare triple $\lbrace I \wedge b \rbrace\ c\ \lbrace I \rbrace$ is valid,
then so is the triple
$\lbrace I \rbrace\ \mathtt{while}\ b\ \mathtt{do}\ c\ \lbrace I \wedge \neg b \rbrace$.
