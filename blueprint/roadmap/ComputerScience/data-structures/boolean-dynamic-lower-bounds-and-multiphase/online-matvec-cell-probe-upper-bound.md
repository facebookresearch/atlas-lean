# Larsen–Williams cell-probe and word-RAM algorithms for online matrix-vector multiplication

Online Boolean matrix-vector multiplication on an $n \times n$ matrix admits a succinct cell-probe structure answering each query in $\tilde{O}(n^{7/4})$ probes with $\tilde{O}(n^{7/4})$ extra bits, and a word-RAM algorithm that answers $n$ online queries in total time $n^3 / 2^{\Omega(\sqrt{\log n})}$. Thus the cell-probe analogue of the OMv conjecture is false, and its word-RAM form can at best be true up to subpolynomial factors.

## Proof sketch

The cell-probe structure stores products of $M$ with a carefully chosen family of sparse vectors and answers a query by decomposing $v$ into a part of low Hamming weight, handled from the stored products, and a part handled by reading rows of $M$, balancing the two at exponent $7/4$. The word-RAM algorithm batches the online queries using Williams' polynomial method for orthogonal vectors and matrix products over a small number of rows at a time.

## Depends on

- [Succinct Boolean matrix-vector multiplication](succinct-boolean-matvec-problem.md)

## Proof depends on

- [Succinct Boolean matrix-vector multiplication](succinct-boolean-matvec-problem.md)

## Sources

- Kasper Green Larsen, Ryan Williams, "Faster Online Matrix-Vector Multiplication", SODA (2017), arXiv:1605.01695.
