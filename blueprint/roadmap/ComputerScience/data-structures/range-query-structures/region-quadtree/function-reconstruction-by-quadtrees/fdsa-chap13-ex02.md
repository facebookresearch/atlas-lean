# Correctness of function reconstruction by quadtrees

For every function $f$ from pairs of natural numbers to a type $A$ and all $n, i, j \in \mathbb{N}$:
if $(i, j)$ lies in the square region of scale $n$, that is $i < 2^n$ and $j < 2^n$, then the
lookup of the cell $(i, j)$ at scale $n$ in the quadtree of scale $n$ sampled from $f$ equals
$f(i, j)$.

## Sources

- T. Nipkow (ed.), *Functional Data Structures and Algorithms: A Proof Assistant Approach*, ACM
  Books, 2025 (author's version of 27 July 2026: https://fdsa-book.net/), Section 13.1, Exercise 13.2.
