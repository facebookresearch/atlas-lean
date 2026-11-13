# Membership in a join of projections

Let $r$ be a relation over a schema $R$ and let
$S_1, \dots, S_n$ be a list of schemes, each contained in $R$. A tuple $t$ belongs to the natural
join of the projections $\pi_{S_1} r, \dots, \pi_{S_n} r$ if and only if $t$ is a tuple over
$S_1 \cup \dots \cup S_n$ and, for every $i$, the restriction of $t$ to $S_i$ belongs to
$\pi_{S_i} r$.
