# Unfolding equation for the while denotation

For every Boolean expression $b$, IMP command
$c$ and states $s$ and $s'$, the relational denotation of $\mathtt{while}\ b\ \mathtt{do}\ c$
relates $s$ to $s'$ if and only if either $b$ evaluates to false in $s$ and $s' = s$, or $b$
evaluates to true in $s$ and there is a state $m$ such that the denotation of $c$ relates $s$ to
$m$ and the denotation of the loop relates $m$ to $s'$.
