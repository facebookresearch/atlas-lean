# A mistake costs weight

Let $K$ be a linearly ordered field, let $\beta \in K$ with
$\beta \le 1$, let $w$ be weights in $K$ on $n$ experts, and let $r$ be a round on which the
weighted majority vote under $w$ differs from the true outcome. If $W$ is the total weight of $w$
and $W'$ is the total weight after updating $w$ on $r$ with penalty $\beta$, then
$2 W' \le (1 + \beta) W$.

At least half of the weight was on the wrong side, and that side keeps only a $\beta$ fraction of
its weight.
