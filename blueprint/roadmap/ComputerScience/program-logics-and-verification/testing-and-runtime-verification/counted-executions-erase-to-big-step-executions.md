# Counted executions erase to big-step executions

Let $s \Downarrow_n f$ mean that the IMP command $c$ has a big-step execution from $s$ to $f$ entering loop bodies $n$ times in total. Then $c$ has a [big-step execution](../../programming-language-semantics/operational-semantics-of-imp/big-step.md) from $s$ to $f$ exactly when $s \Downarrow_n f$ for some $n$.

## Sources

- J. C. King, "Symbolic execution and program testing", *Communications of the ACM* 19(7):385–394, 1976 (symbolic execution, symbolic values and path conditions).
