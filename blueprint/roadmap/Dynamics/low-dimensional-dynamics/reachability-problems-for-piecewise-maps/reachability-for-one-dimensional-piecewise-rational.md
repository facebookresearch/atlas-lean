# Reachability for one-dimensional piecewise rational maps is undecidable

Point-to-point reachability is undecidable for maps of the real line that are given by rational functions with rational coefficients on finitely many intervals; already one fixed such map has undecidable reachability.

A *piecewise rational map* (PRM) is a function $P$ defined on a finite sequence of disjoint intervals $I_- = (-\infty, r_-]$, $I_+ = [l_+, +\infty)$ and $I_i = [l_i, r_i]$ for $i = 1, \ldots, k$, with $r_-, l_+, l_i, r_i \in \mathbb{Q}$, which on each interval is given by a rational function $P(x) = p(x)/q(x)$, a ratio of polynomials. The *reachability problem* asks, given two points $x, y \in \mathbb{Q}$ and a one-dimensional piecewise map $P$, whether $y$ is reachable from $x$, that is, whether $P^k(x) = y$ for some $k \ge 0$.

**Theorem.** The reachability problem for one-dimensional piecewise rational maps with a finite number of intervals is undecidable (Corollary 2 of the source). Moreover, there is a particular one-dimensional piecewise rational map, corresponding to a universal Minsky machine, for which the point-to-point reachability problem is undecidable (Corollary 3).

The rational functions used have degree $2$, and two of the intervals of the construction are unbounded. For piecewise affine maps of the line, a subclass, the source records the reachability problem as open, while for piecewise affine maps of the plane it is undecidable.

## Depends on

None.

## Proof depends on

- [Two-counter machines are universal](../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

A configuration $[k, l, s]$ of a two-counter (Minsky) machine with states $1, \ldots, n$ is encoded by the rational number

$$
x = \frac{1}{10^H}\Bigl(s + \frac{1}{2^{k+1} 3^{l+1}}\Bigr), \qquad H = \lceil \lg n \rceil ,
$$

so the state selects an interval of length $10^{-H}$ and the counters are stored in the fraction. The machine is first replaced by an equivalent one in which a single counter holds $2^c 3^d$ and the exponents serve as virtual counters, so that increments and decrements become multiplications and divisions by $2$ and $3$. Expressions of the form $(10^H x - s) 2^a 3^b + s$, divided by $10^H$, multiply or divide the virtual counters, and auxiliary rational functions of degree $2$ temporarily copy the counter values into the integer part of the number to test divisibility, that is, to test a counter for zero. Each operation of the machine is thus realized by the map on a suitable interval (Theorem 4: piecewise rational maps are a universal model of computation), and reachability of the point encoding the halting configuration is undecidable. The source also shows that one-dimensional piecewise affine maps are equivalent to planar pseudo-billiard ("strange billiard") systems (Theorems 1 to 3).

## Sources

- O. Kurganskyy, I. Potapov and F. Sancho-Caparrini, "Reachability problems in low-dimensional iterative maps", International Journal of Foundations of Computer Science 19 (2008), no. 4, 935–951, https://doi.org/10.1142/S0129054108006054; read in the authors' open-access copy at https://idus.us.es/server/api/core/bitstreams/40854e72-8a40-42de-8f4f-52975b17e0e1/content (Definitions 8 and 9, Problem 1, Theorems 1 to 4 and Corollaries 2 and 3 of that copy, whose numbering may differ from the journal's).
