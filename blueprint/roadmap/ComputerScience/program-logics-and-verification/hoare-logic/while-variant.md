# Variant rule for while loops

Let $I$ be an assertion (the invariant), $V$ a function
from states to natural numbers (the variant), $b$ a Boolean guard and $c$ a command. Suppose
that for every state $s$ satisfying $I$ in which $b$ evaluates to true, there is a terminating
big-step execution of $c$ from $s$ ending in a state $s'$ that satisfies $I$ with
$V(s') < V(s)$. Then the total-correctness Hoare triple with precondition $I$, command
$\mathtt{while}\ b\ \mathtt{do}\ c$ and postcondition "$I$ holds and $b$ evaluates to false"
is valid.
