# The weakest-precondition triple is derivable in total-correctness Hoare logic

For every
IMP command $c$ and every assertion $Q$ (a predicate on states), the triple
$\{\mathrm{wp}(c, Q)\}\,c\,\{Q\}$ is derivable in the total-correctness Hoare logic. Here
$\mathrm{wp}(c, Q)$ is the semantic weakest precondition: it holds in a state $s$ exactly when
there is a terminating execution of $c$ from $s$ ending in a state satisfying $Q$.
