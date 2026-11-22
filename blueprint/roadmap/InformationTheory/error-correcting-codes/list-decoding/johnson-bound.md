# Johnson bound

Let $S$ be a set of words of length $n$ over a finite alphabet, any two distinct at Hamming
distance at least $d$, all within distance $e$ of a word $y$. Suppose $e \le n$, $d \le n$ and

$$n (n - d) < (n - e)^2, \quad\text{that is,}\quad e < n - \sqrt{n (n - d)}.$$

Then

$$|S| \bigl((n - e)^2 - n (n - d)\bigr) \le n (d - e);$$

both factors in brackets are positive under the hypothesis. So a code of minimum distance $d$ has
at most $n (d - e) / ((n - e)^2 - n(n - d))$ codewords in any ball of radius $e$, in particular at
most $n d$ ([list size $n d$](card-le-mul-of-johnson.md)).

This is the strict-inequality case of the alphabet-free Johnson bound, Theorem 7.3.3 of
Guruswami, Rudra and Sudan, with an explicit list size (they give $q n d$; their Exercise 7.5
improves it to $n$ for radius at most $n - \sqrt{n(n-d)} - 1$, so $n d$ is not the best
alphabet-free list size). The proof is the
double-counting argument they give for the binary case of Theorem 7.3.1: with $m_j$ the number of
words of $S$ agreeing with $y$ in coordinate $j$,

- $\sum_j m_j \ge |S| (n - e)$, since each word agrees with $y$ in at least $n - e$ places;
- $\sum_j m_j (m_j - 1) \le |S| (|S| - 1)(n - d)$, since two distinct words agreeing with $y$ in a
  coordinate agree with each other there, which happens in at most $n - d$ coordinates;
- $(\sum_j m_j)^2 \le n \sum_j m_j^2$ by Cauchy–Schwarz,

and the three combine into the stated inequality.

## Informally uses

- [Agreements of two words](card-filter-eq.md): the conversion between agreements and Hamming distance.

## Background

- [Hamming bound](../bounds-on-code-size/hamming-sphere-packing-bound.md): balls of radius
  $\lfloor (d-1)/2 \rfloor$ around codewords are disjoint, so the list size there is $1$. The
  Johnson radius $n - \sqrt{n(n-d)}$ is at least $d/2$ (as $(1 - s/2)^2 \ge 1 - s$), so list
  decoding up to it goes beyond unique decoding.
- [Reed–Solomon codes are list decodable up to the Johnson radius](card-le-of-agree-ge.md): the
  bound for the MDS codes, $d = n - k + 1$, where it gives the radius $1 - \sqrt{R}$, which the
  Guruswami–Sudan algorithm reaches with the parameters of Theorem 12.2.12.

## Sources

- S. M. Johnson, "A new upper bound for error-correcting codes", *IRE Transactions on Information Theory* 8 (1962), 203–207.
- V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*, draft of August 26, 2025, Theorems 7.3.1 and 7.3.3.
