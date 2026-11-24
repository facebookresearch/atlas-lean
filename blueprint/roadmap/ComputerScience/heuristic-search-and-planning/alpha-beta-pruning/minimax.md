# Minimax value

Let values lie in a bounded linear order. The minimax value of a game tree
with player $p$ to move (the maximizer or the minimizer) is defined recursively: a leaf is worth
the value it carries; an inner node is worth, for the maximizer, the maximum of the minimax values
of its children with the minimizer to move, and for the minimizer, the minimum of the minimax
values of its children with the maximizer to move. An inner node without children is worth $\bot$
to the maximizer and $\top$ to the minimizer.
