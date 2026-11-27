# Soundness of bounded symbolic execution

Run bounded symbolic execution with budget $k$ on an IMP command $c$ from the initial store: assignments update the symbolic store with the substituted expression, a conditional splits on its guard and its negation, each loop-body entry increases the cost by one, a path whose cost has reached $k$ is cut off when its loop guard holds, and a branch is pruned only when its substituted guard folds to the literal false. For every terminated symbolic path $q$ and initial state $s$ satisfying the guard of $q$, $c$ runs from $s$ to the evaluation of the store of $q$ at $s$, entering loop bodies exactly the cost of $q$ times, and that cost is at most $k$.

## Sources

- J. C. King, "Symbolic execution and program testing", *Communications of the ACM* 19(7):385–394, 1976 (symbolic execution, symbolic values and path conditions).
