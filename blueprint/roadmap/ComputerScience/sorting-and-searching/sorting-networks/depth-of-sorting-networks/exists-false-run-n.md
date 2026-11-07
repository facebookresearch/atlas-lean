# Comparators inside $(0, n)$ keep a false value inside $(0, n)$

Let $n$ be a natural
number, let $p$ be a list of comparators, each joining two wires in $[0, n)$, and let $f$ assign a
Boolean value to each wire in $\mathbb{N}$. If $f(y)$ is false for some $y < n$, then after
running $p$ on $f$ some wire $y < n$ carries the value false.

The smaller value moves to the first wire of each comparator.
