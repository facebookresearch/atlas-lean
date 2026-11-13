# Trace-zero elements with Galois orbits of full size

Let $K$ be a finite field
extension of a finite field $F$ and $n = [K : F]$. The number of $z \in K$ with
$\operatorname{Tr}_{K/F}(z) = 0$ whose Galois orbit, the set of all $\sigma(z)$ with $\sigma$ an
automorphism of $K$ fixing $F$, has exactly $n$ elements equals the number of tuples
$a = (a_0, \dots, a_{n-1}) \in F^n$ with $a_0 + a_1 + \dots + a_{n-1} = 0$ for which there is no
$l$ with $0 < l < n$ such that $a_{i+l} = a_i$ for all $i$ (indices taken mod $n$).

The trace condition, present in Corollary 9.9 of the arXiv text, cannot be dropped: for
$F = \mathbb{F}_2$ and $n = 3$ there are $6$ elements with Galois orbits of size $3$ but only $3$
such tuples.

## Sources

- Darij Grinberg and Peter Mao, *Necklaces over a Group with Identity Product*, Journal of Integer Sequences 29 (2026), Article 26.4.6, Corollary 33 (`jis-2026-26.4.6-cor-33`).
