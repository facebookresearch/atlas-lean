# Weakest-precondition unfolding of a while loop

For a Boolean guard $b$, a loop body
$c$, a postcondition $Q$ and a state $s$, the state $s$ satisfies the total-correctness weakest
precondition $\mathrm{wp}(\mathtt{while}\ b\ \mathtt{do}\ c, Q)$ if and only if either $b$
evaluates to false in $s$ and $s$ satisfies $Q$, or $b$ evaluates to true in $s$ and $s$
satisfies $\mathrm{wp}(c, \mathrm{wp}(\mathtt{while}\ b\ \mathtt{do}\ c, Q))$.
