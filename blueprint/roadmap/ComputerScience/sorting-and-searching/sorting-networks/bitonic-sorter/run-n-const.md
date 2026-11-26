# Constant blocks stay constant

Let $\alpha$ be a linear order, let $l, h \in \mathbb{N}$,
and let $c$ be a list of comparators on $\mathbb{N}$-indexed wires each of which joins two wires
$x$ with $l \le x < h$. If an input $f : \mathbb{N} \to \alpha$ takes the same value $a$ on
every wire $x$ with $l \le x < h$, then running $c$ on $f$ gives an output that also takes the
value $a$ on every such wire.
