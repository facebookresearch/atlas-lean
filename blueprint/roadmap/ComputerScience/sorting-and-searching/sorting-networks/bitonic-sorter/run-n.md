# Running a comparator network on natural-number-indexed wires

Let $\alpha$ be a
linear order. Given a list $ps$ of comparators, each a pair $(i, j)$ of natural numbers, and
an input $f : \mathbb{N} \to \alpha$ giving the value on each wire, running $ps$ on $f$
applies the comparators of $ps$ to the wire values one after another, from first to last. The
comparator $(i, j)$ puts the minimum of the values on wires $i$ and $j$ on wire $i$ and their
maximum on wire $j$, and leaves the other wires unchanged.
