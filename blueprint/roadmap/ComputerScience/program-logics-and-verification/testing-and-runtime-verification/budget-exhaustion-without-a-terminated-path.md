# Budget exhaustion without a terminated path

In bounded symbolic execution with budget $k$ of an IMP command $c$, as in [soundness of bounded symbolic execution](soundness-of-bounded-symbolic-execution.md): if no terminated symbolic path has a guard true at the initial state $s$, then some cut-off path has a guard true at $s$, and every execution of $c$ from $s$ enters loop bodies more than $k$ times.

## Sources

- J. C. King, "Symbolic execution and program testing", *Communications of the ACM* 19(7):385–394, 1976 (symbolic execution, symbolic values and path conditions).
