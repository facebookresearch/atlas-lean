# States of the CEK machine

For the CEK machine, with untyped de Bruijn lambda terms, closures $\langle t, e\rangle$, environments given by lists of closures, and continuations, a *machine state* is either $\mathsf{eval}(t, e, k)$, evaluating a term $t$ in an environment $e$ under a continuation $k$, or $\mathsf{ret}(v, k)$, returning a closure $v$ to a continuation $k$.

## Sources

- M. Felleisen and D. P. Friedman, *Control operators, the SECD-machine, and the λ-calculus*, 3rd Working Conference on the Formal Description of Programming Concepts, 1986. The machine here is a de Bruijn reformulation for the pure lambda calculus, without the control operators of that paper.
