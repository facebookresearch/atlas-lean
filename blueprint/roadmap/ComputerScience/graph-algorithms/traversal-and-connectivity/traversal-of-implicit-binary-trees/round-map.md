# Commuting maps transport one depth-first round

Let $\sigma_1$ be a branching step on states $S_1$, $\sigma_2$ a branching step on states $S_2$,
and $f : S_1 \to S_2$ a map commuting with them: for every $x \in S_1$, $f(x)$ is terminal for
$\sigma_2$ exactly when $x$ is terminal for $\sigma_1$, and if $x$ branches into $(l, h)$ then
$f(x)$ branches into $(f(l), f(h))$. Then for every pair (stack, output) of lists over $S_1$,
one depth-first round for $\sigma_2$ applied to the images under $f$ of the stack and the output
gives the images under $f$ of the stack and the output of one round for $\sigma_1$.
