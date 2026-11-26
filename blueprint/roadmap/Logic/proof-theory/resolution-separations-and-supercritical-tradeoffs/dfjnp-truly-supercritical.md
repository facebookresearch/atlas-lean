# de Rezende–Fleming–Janett–Nordström–Pang: truly supercritical trade-offs for resolution and cutting planes

There are explicit families of unsatisfiable CNF formulas with polynomial-size resolution refutations such that every resolution or cutting planes refutation of size at most a superpolynomial threshold must have depth superlinear (in some regimes superpolynomial) in the formula size, giving the first truly supercritical size-depth trade-offs for these systems. Moreover, there are truly supercritical trade-offs between width and size for tree-like resolution, and robust supercritical trade-offs between dimension and iteration number for the Weisfeiler-Leman algorithm, equivalently between the number of variables and quantifier depth in first-order logic with counting.

## Proof sketch

The base result is a supercritical width-depth trade-off for resolution obtained by refining and strengthening the compression scheme for the cops-and-robber game on suitable graphs. Improved dag-like and tree-like lifting theorems transfer it to cutting planes, tree-like resolution and monotone circuits, while the correspondence between the cops-and-robber game and the bijective pebble game gives the Weisfeiler-Leman statement.

## Depends on

- [Supercritical trade-offs in proof complexity](supercritical-tradeoff.md)
- [Cutting planes lower bounds for lifted formulas via real dag-like lifting](../stabbing-planes-and-semi-algebraic-branching/lifted-cp-lower-bounds.md)
- [Truly supercritical depth trade-offs for monotone circuits](../../../TheoryOfComputation/circuit-complexity/monotone-separations-and-supercritical-depth/supercritical-monotone-depth.md)

## Proof depends on

- [Supercritical trade-offs in proof complexity](supercritical-tradeoff.md)
- [Cutting planes lower bounds for lifted formulas via real dag-like lifting](../stabbing-planes-and-semi-algebraic-branching/lifted-cp-lower-bounds.md)
- [Truly supercritical depth trade-offs for monotone circuits](../../../TheoryOfComputation/circuit-complexity/monotone-separations-and-supercritical-depth/supercritical-monotone-depth.md)

## Sources

- S. F. de Rezende, N. Fleming, D. Janett, J. Nordström, S. Pang, "Truly supercritical trade-offs for resolution, cutting planes, monotone circuits, and Weisfeiler-Leman", STOC (2025), arXiv:2411.14267.
