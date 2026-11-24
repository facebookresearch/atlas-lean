# Plotkin bound

Let $C$ be a code of length $n$ over an alphabet with $q$ letters whose distinct codewords are at
Hamming distance at least $d$, where $q d > (q - 1) n$, that is $d > (1 - 1/q) n$. Then

$$|C| \bigl(q d - (q-1) n\bigr) \le q d, \qquad\text{that is}\qquad |C| \le \frac{q d}{q d - (q-1) n}.$$

This is part 2 of Theorem 4.4.1 of Guruswami, Rudra and Sudan. The proof here is the classical
averaging argument: summing $\Delta(c, c')$ over all ordered pairs of codewords gives at least
$|C|(|C| - 1) d$, while in each coordinate at most $(1 - 1/q)|C|^2$ ordered pairs disagree
([disagreeing pairs in a coordinate](disagreeing-pairs-in-a-coordinate.md)). Guruswami, Rudra and
Sudan prove it instead with a geometric lemma on vectors with pairwise non-positive inner products.
Part 1 of the theorem ($d = (1 - 1/q) n$ gives $|C| \le 2 q n$) and the asymptotic consequence
$R \le 1 - \frac{q}{q-1}\delta + o(1)$ (Corollary 4.4.2) complete it.

## Background

- [Disagreeing pairs in a coordinate](disagreeing-pairs-in-a-coordinate.md): the per-coordinate count behind the classical averaging proof given here.
- [Singleton bound](singleton-bound.md): by the Plotkin bound (its asymptotic form, Corollary
  4.4.2), codes meeting the Singleton bound need alphabets that grow with $n$, as Reed–Solomon
  codes have (Guruswami, Rudra and Sudan, Section 5.2).

## Sources

- M. Plotkin, "Binary codes with specified minimum distance", *IRE Transactions on Information Theory* 6 (1960), 445–450.
- V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*, draft of August 26, 2025, Theorem 4.4.1.
