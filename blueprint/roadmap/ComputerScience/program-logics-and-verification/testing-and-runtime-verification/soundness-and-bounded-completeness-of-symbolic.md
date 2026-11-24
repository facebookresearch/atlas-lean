# Soundness and bounded completeness of symbolic execution

Run bounded symbolic execution on an IMP command $c$ from the initial path (guard $\mathrm{true}$, initial store, cost $0$), using
the [symbolic stores and paths](symbolic-expressions-and-symbolic-states.md). Assignments update the store with the
substituted expression, a conditional splits on its guard and its negation, each loop-body entry increases the cost by
one, and a path is cut off once its cost reaches the budget $k$. A branch is pruned only when its substituted guard folds
to the literal $\mathrm{false}$. The result is a finite list of leaves, each a terminated path or a cut-off path. Let
$s \Downarrow_n f$ mean that $c$ has a big-step execution from $s$ to $f$ entering loop bodies $n$ times in total.

- **Substitution.** For every store $\sigma$, expression $e$ and state $s$, evaluating $\sigma(e)$ in $s$ equals evaluating $e$ in the
  state $x \mapsto [\![\sigma(x)]\!]\,s$.
- **Soundness.** For every terminated path $q$ and initial state $s$ satisfying the guard of $q$, $c$ runs from $s$ to the evaluation
  of the store of $q$ at $s$ with exactly the cost of $q$, and that cost is at most $k$.
- **Bounded completeness.** If $s \Downarrow_n f$ with $n \le k$, some terminated path $q$ has guard true at $s$, store evaluating to $f$
  at $s$, and cost $n$.
- **Coverage.** Every initial state satisfies the guard of some leaf, and every cut-off path has cost exactly $k$. If no
  terminated path's guard holds at $s$, then some cut-off path's guard holds at $s$ and every execution of $c$ from $s$
  enters loop bodies more than $k$ times.

Counting loop-body entries does not change big-step executions: $c$ runs from $s$ to $f$ exactly when $s \Downarrow_n f$ for some $n$.

## Depends on

- [Symbolic expressions and symbolic states](symbolic-expressions-and-symbolic-states.md)
- [Big-step semantics of IMP](../../programming-language-semantics/operational-semantics-of-imp/big-step.md)

## Sources

- J. C. King, "Symbolic execution and program testing", *Communications of the ACM* 19(7):385–394, 1976 (symbolic execution and path conditions; the bounded statements here are the formalized results).
