# Commuting maps transport any number of rounds

Let $\sigma_1$ and $\sigma_2$ be branching steps on states $S_1$ and $S_2$, and $f : S_1 \to S_2$
a map commuting with them ($f(x)$ is terminal exactly when $x$ is, and if $x$ branches into
$(l, h)$ then $f(x)$ branches into $(f(l), f(h))$). Then for every $i \in \mathbb{N}$ and every
pair (stack, output) of lists over $S_1$, applying $i$ rounds for $\sigma_2$ to the images under
$f$ of the stack and the output gives the images under $f$ of the stack and output obtained by $i$
rounds for $\sigma_1$. The map $f$ need not be injective.
