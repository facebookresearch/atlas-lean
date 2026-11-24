# Correctness of bottom-up rod cutting

Let $\alpha$ be an additive commutative monoid with a
linear order in which addition is monotone, and let $p = (p_1, \dots, p_n)$ be prices in $\alpha$,
$p_i$ being the price of a piece of length $i$. The value returned by bottom-up rod cutting on $p$
is the greatest revenue of a composition of $n$: it equals $p_{b_1} + \dots + p_{b_m}$ for some
composition $(b_1, \dots, b_m)$ of $n$ into positive parts, and it is at least this sum for every
such composition.

Prices may be negative; every piece of the rod must be sold, so there is no option to discard
material.
