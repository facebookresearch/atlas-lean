# Total weight after an update

Let $\beta$ be an element of a linearly ordered field $K$,
let $w_0, \dots, w_{n-1} \in K$ be weights on $n$ experts, and let $r$ be a round with advice
$a \in \{\mathrm{true}, \mathrm{false}\}^n$ and outcome $y$. If $w'$ are the weights after the
update with penalty $\beta$ on $r$, then
$\sum_{i < n} w'_i = \sum_{i < n} w_i - (1 - \beta) \sum_{i : a_i = \lnot y} w_i$: the experts
that advised wrongly keep a $\beta$ fraction of their weight.
