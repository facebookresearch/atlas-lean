# Closures of the CEK machine

A *closure* of the CEK machine is a pair $\langle t, e\rangle$ of an arbitrary untyped de Bruijn lambda term $t$ and an arbitrary environment $e$. Environments are finite lists of closures, index $0$ first, so closures form a nested inductive type with the single constructor $\langle t, e\rangle$. The type records no invariant: evaluating an abstraction $\lambda.\,t$ in $e$ produces $\langle t, e\rangle$, but closures need not arise that way.

## Sources

- M. Felleisen and D. P. Friedman, *Control operators, the SECD-machine, and the λ-calculus*, 3rd Working Conference on the Formal Description of Programming Concepts, 1986. The machine here is a de Bruijn reformulation for the pure lambda calculus, without the control operators of that paper.
