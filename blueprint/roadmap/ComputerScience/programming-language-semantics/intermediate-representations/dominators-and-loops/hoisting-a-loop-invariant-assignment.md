# Hoisting a loop-invariant assignment

Let $L$ be a [natural loop](back-edges-and-natural-loops.md) with header $h$ in a control-flow graph whose instructions are assignments of expressions without side effects that cannot fail, and conditional branches. Give $L$ a *preheader*: a new node $p$ that receives every edge entering $h$ from outside $L$ and has the single edge $p \to h$.

- An expression $e$ in $L$ is *loop-invariant* if each variable it uses has all its [reaching definitions](../../static-analysis/classical-dataflow-analyses/reaching-definitions-analysis.md) outside $L$, or has exactly one reaching definition, located in $L$, whose right-hand side is loop-invariant. The loop-invariant expressions are the greatest set closed under this condition, computed by iteration from the set of all expressions of $L$.
- An assignment $x \leftarrow e$ in $L$ with $e$ loop-invariant *may be hoisted* if it is the only definition of $x$ in $L$, it dominates every exit of $L$ at which $x$ is [live](../../static-analysis/live-variables-analysis.md) on leaving, and $x$ is not live on entry to $h$.

**Claim.** Moving an assignment that may be hoisted from $L$ to the end of the preheader preserves the observable behavior of the program.

## Depends on

- [Back edges and natural loops](back-edges-and-natural-loops.md)
- [Reaching definitions analysis](../../static-analysis/classical-dataflow-analyses/reaching-definitions-analysis.md)
- [Live-variables analysis](../../static-analysis/live-variables-analysis.md)

## Expansion

This node is a family still to break down:

- a small-step semantics of the control-flow-graph language with its observable behaviors, and the preheader transformation with its proof of semantic preservation (statement prerequisites);
- a source that proves the claim: the cited notes give the conditions without a proof, and the assumptions on expressions (no side effects, no failure, no nontermination) must be matched to the semantics chosen.

## Sources

- A. C. Myers, *Control-flow analysis*, lecture notes for CS 4120, Cornell University, 2022, <https://courses.cs.cornell.edu/courses/cs4120/2022sp/notes/cflow/index.html>: section "Loop-invariant code motion": the iterative computation of loop-invariant expressions from reaching definitions, starting from all expressions of the loop; the three conditions for moving an assignment $x \leftarrow e$ before the loop header; and the requirement not to hoist expressions that might raise an exception.
