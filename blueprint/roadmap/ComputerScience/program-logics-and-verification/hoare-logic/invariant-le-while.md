# Loop invariants entail the weakest liberal precondition of the loop

Let $I$ and $Q$
be assertions, $b$ a Boolean expression and $c$ a command. Suppose that every state satisfying
$I$ in which $b$ evaluates to true satisfies the weakest liberal precondition of $c$ with
respect to $I$, and that every state satisfying $I$ in which $b$ evaluates to false satisfies
$Q$. Then $I$ entails the weakest liberal precondition of the loop
$\mathtt{while}\ b\ \mathtt{do}\ c$ with respect to $Q$.
