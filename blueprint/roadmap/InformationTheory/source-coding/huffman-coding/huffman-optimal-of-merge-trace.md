# A two-minimum merge trace gives a minimum weighted path length

Let $L$ be a list of
symbol–weight pairs with natural-number weights, and let $t$ and $t'$ be coding trees with
symbols of the same type. Suppose the weighted path length of $t$, as a real number, is the cost
of a two-minimum merge trace for the multiset of the weights of $L$, taken as reals (repeatedly
replace two weights $x \le y$, with every other weight at least $y$, by $x + y$ until one weight
remains, the cost being the sum of the sums formed), and that the weighted leaves of $t'$, listed
left to right, are a permutation of $L$. Then the weighted path length of $t$ is at most that of
$t'$.
