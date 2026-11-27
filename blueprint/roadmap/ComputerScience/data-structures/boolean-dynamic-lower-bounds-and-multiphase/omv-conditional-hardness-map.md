# Conditional hardness from OMv versus unconditional cell-probe bounds

Under the OMv conjecture, dynamic subgraph connectivity and many other dynamic graph problems on $n$ vertices have polynomial conditional lower bounds on update or query time, of the form stated for subgraph connectivity on the corresponding fine-grained page. Such bounds cannot be reproduced unconditionally in the cell-probe model by proving the OMv hypothesis there: the cell-probe analogue of OMv is false, since online Boolean matrix-vector multiplication has succinct cell-probe structures with $\tilde{O}(n^{7/4})$-probe queries. The unconditional dynamic cell-probe lower bounds given by the information-transfer, cell-sampling and multiphase-game methods are polylogarithmic in $n$, at most $\Omega((\lg n/\lg\lg n)^2)$ for $w = \Theta(\lg n)$ and polylogarithmic update time.

## Proof sketch

The conditional statement is the OMv-to-dynamic-problem reduction of Henzinger, Krinninger, Nanongkai and Saranurak specialized to subgraph connectivity. The contrast follows from the Larsen–Williams cell-probe structure, which refutes the cell-probe version of the hypothesis, together with Ko's $\Omega((\lg n/\lg\lg n)^2)$ multiphase bound and Larsen's matching bound for weighted range counting.

## Depends on

- [The online matrix-vector multiplication conjecture](../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-online-matrix-vector-multiplication.md)
- [Dynamic graph problems](../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/dynamic-graph-problems.md)
- [The cell-probe model](../range-query-structures/advanced-data-structures/the-cell-probe-model.md)

## Proof depends on

- [Larsen–Williams cell-probe and word-RAM algorithms for online matrix-vector multiplication](online-matvec-cell-probe-upper-bound.md)
- [Boolean dynamic lower bounds reach the weighted $\log^2$ bound](boolean-matches-weighted-barrier.md)
- [OMv-hardness of dynamic subgraph connectivity](../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/omv-hardness-of-dynamic-subgraph-connectivity.md)

## Sources

- Monika Henzinger, Sebastian Krinninger, Danupon Nanongkai, Thatchaphol Saranurak, "Unifying and Strengthening Hardness for Dynamic Problems via the Online Matrix-Vector Multiplication Conjecture", STOC (2015), arXiv:1511.06773.
- Kasper Green Larsen, Ryan Williams, "Faster Online Matrix-Vector Multiplication", SODA (2017), arXiv:1605.01695.
