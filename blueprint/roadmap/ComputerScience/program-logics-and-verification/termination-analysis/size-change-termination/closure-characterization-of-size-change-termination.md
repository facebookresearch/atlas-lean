# Closure characterization of size-change termination

The *composition* $G ; G' : f \to h$ of size-change graphs $G : f \to g$ and $G' : g \to h$ has an edge $x \xrightarrow{\downarrow} z$ if there are $y$ and edges $x \to y$ in $G$ and $y \to z$ in $G'$ at least one of which is labelled $\downarrow$, and an edge $x \xrightarrow{\overline{\downarrow}} z$ if there are such edges but none of these paths contains a $\downarrow$ edge. Composition is associative; for a finite call sequence $cs = c_1 \cdots c_n$ let $G_{cs} = G_{c_1} ; \dots ; G_{c_n}$, and let

$$\mathcal{S} = \{ G_{cs} : cs \text{ and } cs' \text{ are call sequences with } f_{\mathrm{init}} \xrightarrow{cs'} f \xrightarrow{cs} g \},$$

a finite set. Then the program is not [size-change terminating](size-change-graphs.md) if and only if $\mathcal{S}$ contains a graph $G : f \to f$ with $G = G ; G$ that has no edge of the form $x \xrightarrow{\downarrow} x$. This yields an algorithm: compute $\mathcal{S}$ by closing the graphs of the reachable calls under composition, then test each idempotent graph from a function to itself.

## Expansion

This page becomes ready once these prerequisites are stated:

- The infinite Ramsey theorem for pairs (proof prerequisite)

## Depends on

- [Size-change graphs and size-change termination](size-change-graphs.md)

## Sources

- P. M. Neergaard, *The Size-Change Principle of Termination*, lecture notes, Brandeis University, <https://www.cs.brandeis.edu/~cs117a/size-change-termination.pdf>, Section 5, Definitions 5.1 and 5.3, Theorem 5.4 and the algorithm that follows it.
