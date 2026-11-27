# Parity of the order of vanishing from a functional equation

Let $F \colon \mathbb{C} \to \mathbb{C}$ be an entire function that is not identically zero, and let $w \in \{1, -1\}$
with $F(s) = w F(2 - s)$ for all $s$. Let $m \ge 0$ be the order of vanishing of $F$ at $s = 1$. Then $(-1)^m = w$: $m$
is even if $w = 1$ and odd if $w = -1$. In particular, if $w = -1$ then $F(1) = 0$.

Proof (worked out here): write $F(1 + h) = \sum_{k \ge 0} c_k h^k$; the functional equation gives
$\sum_k c_k h^k = w \sum_k c_k (-h)^k$, so $c_k = w(-1)^k c_k$ for all $k$, and $c_m \ne 0$ forces $w(-1)^m = 1$.

## Sources

- H. Darmon, *Rational points on modular elliptic curves*, CBMS Regional Conference Series in Mathematics 101,
  American Mathematical Society, 2004; author's version,
  <https://www.math.mcgill.ca/darmon/pub/Articles/Research/36.NSF-CBMS/chapter.pdf>, cited by the page numbers
  printed in that version: p. 21 ("Note that $L(E, s)$ vanishes to even (resp. odd) order at $s = 1$ when $\operatorname{sign}(E, \mathbb{Q}) = 1$
  (resp. $\operatorname{sign}(E, \mathbb{Q}) = -1$)."), the consequence of the functional equation that this page states for
  an arbitrary entire function.
