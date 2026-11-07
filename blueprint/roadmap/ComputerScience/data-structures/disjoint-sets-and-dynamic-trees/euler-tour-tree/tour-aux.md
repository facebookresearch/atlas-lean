# Euler tour with an accumulator

Let $t$ be a tree with root $r$ and child subtrees
$c_1, \dots, c_k$ in order, and let $a$ be a list of vertices. For a list $L$ of vertices, write
$r \cdot L$ for the list $L$ with $r$ put in front. The Euler tour of $t$ with accumulator $a$,
written $T(t, a)$, is $r \cdot L_1$, where $L_{k+1} = a$ and $L_i = T(c_i, r \cdot L_{i+1})$ for
$i = k, \dots, 1$.

It equals the Euler tour of $t$ followed by $a$, and computes the Euler tour without repeatedly
concatenating the tours of the child subtrees.
