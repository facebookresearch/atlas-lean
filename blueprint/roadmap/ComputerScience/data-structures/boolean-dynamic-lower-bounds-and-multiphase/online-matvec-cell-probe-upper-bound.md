# Larsen–Williams cell-probe and word-RAM algorithms for online matrix-vector multiplication

Online Boolean matrix-vector multiplication on an $n \times n$ matrix with $w$-bit cells, $w = \Theta(\log n)$, admits a deterministic cell-probe structure that stores the matrix plus $O(n^{7/4}\sqrt{w})$ extra bits and computes $Mv$ for every query vector $v$ with $O(n^{7/4}/\sqrt{w})$ probes in the worst case, that is $\tilde{O}(n^{7/4})$ bits and probes (Theorem 1.3, which writes the bound for a general word size $w$; the expression counts at least one probe only while $w \le n^{7/2}$, and $w = \Theta(\log n)$ keeps it meaningful). In the word-RAM model, with no preprocessing, any sequence of $t = 2^{\omega(\sqrt{\log n})}$ online queries is answered with high probability in $n^2/2^{\Omega(\sqrt{\log n})}$ amortized randomized time per query (Theorem 1.1), so $n$ queries take $n^3/2^{\Omega(\sqrt{\log n})}$ time. Thus the cell-probe analogue of the OMv conjecture is false, while the word-RAM bound improves on $n^3$ only by a subpolynomial factor and does not refute the conjecture.

## Proof sketch

By the Henzinger–Krinninger–Nanongkai–Saranurak reduction, an $Mv$ query reduces to $O(n)$ vector-matrix-vector queries $u^\top A v$ on the $n$ blocks $A$ of size $\sqrt{n} \times \sqrt{n}$. For an $m \times m$ block the cell-probe structure greedily stores a list of all-zero rectangles $U \times V$, each covering at least $m^{3/2}/\sqrt{w}$ new entries, so the list has at most $m^{1/2}\sqrt{w}$ rectangles; a query reads the list, and if more than $m^{3/2}/\sqrt{w}$ entries of its rectangle are uncovered the answer is $1$, otherwise it reads the uncovered entries. With $m = \sqrt{n}$ this gives $O(n^{3/4}/\sqrt{w})$ probes per block query. The word-RAM algorithm reduces the vector-matrix-vector queries to listing orthogonal pairs among Boolean vectors of dimension $2^{O(\sqrt{\log n})}$, which is solved with small algebraic matrix products.

## Depends on

- [Succinct Boolean matrix-vector multiplication](succinct-boolean-matvec-problem.md)
- [The online matrix-vector multiplication conjecture](../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-online-matrix-vector-multiplication.md)
- [The cell-probe model](../range-query-structures/advanced-data-structures/the-cell-probe-model.md)

## Sources

- Kasper Green Larsen, Ryan Williams, "Faster Online Matrix-Vector Multiplication", SODA (2017), arXiv:1605.01695.
