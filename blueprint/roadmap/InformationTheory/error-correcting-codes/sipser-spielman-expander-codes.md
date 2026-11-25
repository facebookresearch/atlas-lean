# Sipser-Spielman expander codes

Let $G$ be a bipartite graph with $n$ left vertices of degree $D \ge 1$ and parity checks given by the right vertices.
Suppose every nonempty left set $S$ with $\lvert S \rvert \le \alpha n$ has more than $\tfrac34 D \lvert S \rvert$ neighbours.
Then the code has minimum distance greater than $\alpha n$, and the bit-flipping decoder (repeatedly flip a bit with
more unsatisfied than satisfied checks) corrects every error pattern of weight at most $\alpha n/2$: it stops after at most
$D \lfloor \alpha n/2 \rfloor$ flips, each changing the status of $D$ checks, and with bounded left and right degrees it runs in
time $O(n)$ (Sipser–Spielman).

## Depends on

- [Linear code](linear-codes/linear-code.md)
- [Minimum distance](linear-codes/min-dist.md)

## Proof depends on

- [Expander code distance](expander-code-distance.md)

## Sources

- V. Guruswami, *Introduction to Coding Theory*, Carnegie Mellon University lecture notes, Spring 2010, Notes 8,
  Section 1.1 (Lemmas 5 and 6, Sections 1.1.1 and 1.1.2: the flipping decoder for expansion above $3D/4$ and its running
  time). <https://www.cs.cmu.edu/~venkatg/teaching/codingtheory/notes/notes8.pdf>
- V. Guruswami, A. Rudra and M. Sudan, *Essential Coding Theory*, draft of August 26, 2025, Lemma 11.3.4 and
  Theorem 11.3.6 (distance). <https://cse.buffalo.edu/faculty/atri/courses/coding-theory/book/web-coding-book.pdf>
- M. Sipser and D. A. Spielman, Expander codes, IEEE Trans. Inform. Theory 42(6) (1996), 1710–1722, as cited in
  *Essential Coding Theory*, Section 11.6.
