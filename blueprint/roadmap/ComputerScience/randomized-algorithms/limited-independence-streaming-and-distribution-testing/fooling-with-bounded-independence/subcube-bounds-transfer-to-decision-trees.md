# Subcube bounds transfer to adaptive decision-tree tests

Let $d$ be a signed weight function on $\{0,1\}^n$ and call a set of coordinates admissible if the total weight of $d$ on every subcube fixing exactly those coordinates is at most $\varepsilon$ in absolute value. Let $T$ be a decision tree on $\{0,1\}^n$ that, on every input, queries at most $k$ distinct coordinates forming an admissible set, and let $g$ be a function of its leaves with $|g| \le C$. Then

$$
\Bigl|\sum_{z} d(z)\,g(T(z))\Bigr| \le 2^k C\varepsilon .
$$

## Proof sketch

An input reaches a leaf exactly on the subcube of inputs agreeing with it on the queried coordinates. Induct over the tree, carrying the partial assignment fixed so far: a query whose answer is already fixed follows one branch, so repeated queries cost nothing, and each leaf contributes at most $C\varepsilon$ over at most $2^k$ leaves reached (a reached leaf is determined by the answers to at most $k$ distinct queries).

## Depends on

- [Binary decision tree](../../../../Combinatorics/boolean-functions/osss-inequality-for-decision-trees/decision-tree.md)

## Sources

- O. Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008.
