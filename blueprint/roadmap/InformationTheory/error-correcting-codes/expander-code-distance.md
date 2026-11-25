# Expander code distance

Let $G$ be a bipartite graph with $n$ left vertices, each of degree $D \ge 1$, and let $C$ be the binary code of vectors in
$\mathbb{F}_2^n$ whose restriction to the neighbourhood of every right vertex has even parity. A right vertex is a unique
neighbour of a left set $S$ if it has exactly one neighbour in $S$. If every nonempty left set $S$ with
$\lvert S \rvert \le \alpha n$ has at least one unique neighbour (for example, if it has more than $(D/2)\lvert S \rvert$
neighbours in total, which forces unique neighbours), then every nonzero codeword has weight greater than $\alpha n$, so
the minimum distance of $C$ exceeds $\alpha n$. The conditions quantify over nonempty sets only.

## Depends on

- [Linear code](linear-codes/linear-code.md)
- [Minimum distance](linear-codes/min-dist.md)

## Sources

- V. Guruswami, A. Rudra and M. Sudan, *Essential Coding Theory*, draft of August 26, 2025, Definition 11.3.3, Lemma 11.3.4
  and Theorem 11.3.6; Section 11.6 credits the distance argument to M. Sipser and D. A. Spielman, Expander codes, IEEE
  Trans. Inform. Theory 42(6) (1996). <https://cse.buffalo.edu/faculty/atri/courses/coding-theory/book/web-coding-book.pdf>
