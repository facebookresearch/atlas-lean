# Bounded completeness of symbolic execution

In bounded symbolic execution with budget $k$ of an IMP command $c$, as in [soundness of bounded symbolic execution](soundness-of-bounded-symbolic-execution.md): if $c$ runs from $s$ to $f$ entering loop bodies $n \le k$ times, some terminated symbolic path has guard true at $s$, store evaluating to $f$ at $s$, and cost $n$.

## Sources

- J. C. King, "Symbolic execution and program testing", *Communications of the ACM* 19(7):385–394, 1976 (symbolic execution, symbolic values and path conditions).
