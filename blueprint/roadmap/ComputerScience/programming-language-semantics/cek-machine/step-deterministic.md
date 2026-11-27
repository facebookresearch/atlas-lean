# The CEK machine is deterministic

The CEK machine runs untyped lambda terms in de Bruijn notation ($x_n$, $\lambda.\,t$, $t\,u$) by call-by-value. A *closure* $\langle t, e\rangle$ pairs an arbitrary term $t$ with an environment $e$, a list of closures with index $0$ first. A *continuation* is $\mathsf{mt}$, $\mathsf{arg}(u, e, k)$ (when it receives the value $v$ of the function part, evaluate the argument $u$ in $e$ under $\mathsf{fn}(v, k)$) or $\mathsf{fn}(v, k)$ (when the value of the argument returns, apply the function closure $v$ to it under $k$). A *state* is either $\mathsf{eval}(t, e, k)$ or $\mathsf{ret}(v, k)$ for a closure $v$.

The transitions are:

- $\mathsf{eval}(t\,u, e, k) \to \mathsf{eval}(t, e, \mathsf{arg}(u, e, k))$;
- $\mathsf{eval}(\lambda.\,t, e, k) \to \mathsf{ret}(\langle t, e\rangle, k)$;
- $\mathsf{eval}(x_n, e, k) \to \mathsf{ret}(v, k)$ when $e$ has an entry $v$ at index $n$ (there is no transition when $n$ is at least the length of $e$);
- $\mathsf{ret}(v, \mathsf{arg}(u, e, k)) \to \mathsf{eval}(u, e, \mathsf{fn}(v, k))$;
- $\mathsf{ret}(v, \mathsf{fn}(\langle t, e\rangle, k)) \to \mathsf{eval}(t, v :: e, k)$.

For all states $s, s_1, s_2$, if $s \to s_1$ and $s \to s_2$ then $s_1 = s_2$: every state has at most one successor.

## Sources

- M. Felleisen and D. P. Friedman, *Control operators, the SECD-machine, and the λ-calculus*, 3rd Working Conference on the Formal Description of Programming Concepts, 1986. The machine here is a de Bruijn reformulation for the pure lambda calculus, without the control operators of that paper.
