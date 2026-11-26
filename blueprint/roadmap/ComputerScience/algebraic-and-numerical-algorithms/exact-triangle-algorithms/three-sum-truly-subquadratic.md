# Integer 3SUM in truly subquadratic word-RAM time

For every fixed $\kappa \ge 1$ there is a single deterministic word-RAM program that decides distinct-position 3SUM on $n$ integers of absolute value at most $(n+2)^\kappa$ in time $O_\kappa(n^{1.9992})$, at every word size $w \ge c_\kappa \log_2(n+2)$. In particular the 3SUM hypothesis fails for polynomially bounded integer inputs on the word RAM.

## Proof sketch

Apply the Chan-He reduction, consuming its Convolution-3SUM nodes one at a time during the traversal; reduce each node to $O(\sqrt{N})$ Exact Triangle instances on $O(\sqrt{N})$ vertices per part and run the subcubic Exact Triangle algorithm. The square-root dimension turns the saving $33/20000$ into a polynomial saving over $n^2$ after all frontend and traversal overheads.

## Depends on

- [Distinct-position 3SUM](../three-sum-reductions/distinct-position-three-sum.md)
- [The 3SUM, APSP and Orthogonal Vectors hypotheses](../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-3sum-apsp-and-orthogonal-vectors-hypotheses.md)
- [The word-RAM model](../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Proof depends on

- [Chan-He: 3SUM reduces to polylogarithmically many Convolution-3SUM instances](../three-sum-reductions/chan-he-reduction.md)
- [Convolution-3SUM reduces to Exact Triangle](convolution-three-sum-to-exact-triangle.md)
- [Exact Triangle in truly subcubic word-RAM time](exact-triangle-truly-subcubic.md)

## Sources

- J. Alman and V. Vassilevska Williams, "Truly Subquadratic 3SUM and Truly Subcubic APSP via Triangles in Sparse Lopsided Graphs", arXiv:2610.06783, 2026.
- T. M. Chan and Q. He, "Reducing 3SUM to Convolution-3SUM", Symposium on Simplicity in Algorithms (SOSA), 2020.
