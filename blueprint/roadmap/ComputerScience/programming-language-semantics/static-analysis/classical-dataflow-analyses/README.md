# Classical dataflow analyses

The bit-vector analyses of an optimizing compiler, as instances of [monotone frameworks](../monotone-frameworks-and-the-worklist-algorithm.md) over powerset lattices: reaching definitions (forward, may), available expressions (forward, must) and very busy expressions (backward, must), beside [live variables](../live-variables-analysis.md) (backward, may). Their transfer functions have the gen/kill form, which makes them distributive, so iterative solving reaches the [meet-over-all-paths solution](../meet-over-all-paths-versus-the-fixed-point.md).

- [Reaching definitions analysis](reaching-definitions-analysis.md)
- [Available expressions analysis](available-expressions-analysis.md)
- [Very busy expressions analysis](very-busy-expressions-analysis.md)
- [Gen/kill transfer functions are distributive](gen-kill-transfer-functions-are-distributive.md)
- [Def-use chains and webs](def-use-chains-and-webs.md)
