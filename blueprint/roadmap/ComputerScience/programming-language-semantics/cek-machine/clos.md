# Closures of the CEK machine

A *closure* of the CEK machine is a pair $\langle t, e\rangle$ of an untyped de Bruijn lambda term $t$, the body of an abstraction, and an environment $e$, the environment in which the abstraction was evaluated. Environments are finite lists of closures, index $0$ first, so closures form a nested inductive type with the single constructor $\langle t, e\rangle$.

## Sources

- M. Felleisen and D. P. Friedman, *Control operators, the SECD-machine, and the λ-calculus*, 3rd Working Conference on the Formal Description of Programming Concepts, 1986. The machine here is a de Bruijn reformulation for the pure lambda calculus, without the control operators of that paper.
