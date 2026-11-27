# Correctness of recursive CUT-ROD

Let $\alpha$ be an additive commutative monoid with a
linear order for which addition is monotone, and let $p_1, \dots, p_n \in \alpha$ be prices,
$p_i$ being the price of a piece of length $i$. The value returned by recursive CUT-ROD on these
prices is the greatest revenue of a composition of $n$: it equals the revenue
$p_{i_1} + \dots + p_{i_k}$ of some composition $n = i_1 + \dots + i_k$ into positive parts,
and it is at least the revenue of every such composition.

Every piece is sold: negative prices do not create an option to discard part of the rod.
