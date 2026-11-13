# Influence sets grow at most exponentially with the level

Let $p$ be a list of comparators
on wires indexed by $\mathbb{N}$. Let $S$ assign to each wire a finite set of natural numbers and
let $\ell$ assign to each wire a natural number, such that $|S(x)| \le 2^{\ell(x)}$ for every
wire $x$. For each wire $x$, let $L(x)$ be the level of $x$ after $p$ starting from the levels
$\ell$. Then for every wire $x$, the influence set of $x$ after $p$ starting from $S$ has at most
$2^{L(x)}$ elements.

In particular, a wire at level $l$ depends on at most $2^l$ inputs.
