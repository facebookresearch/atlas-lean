# Huffman's construction follows a two-minimum merge trace

Let $L$ be a list of
symbol–weight pairs with natural-number weights, over a symbol type with decidable equality,
and suppose the Huffman construction returns the tree $t$ on $L$. Then the weighted path length
of $t$, as a real number, is the cost of a two-minimum merge trace for the multiset of the
weights of $L$, taken as reals: starting from that multiset, repeatedly replace two weights
$x \le y$ such that every other weight is at least $y$ by their sum $x + y$, until a single
weight remains; the cost is the sum of all the sums $x + y$ formed.
