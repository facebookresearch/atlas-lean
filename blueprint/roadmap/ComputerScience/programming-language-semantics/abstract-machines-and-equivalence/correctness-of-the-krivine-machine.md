# Correctness of the Krivine machine

Krivine's machine evaluates lambda terms by weak head reduction, that is, call-by-name reduction at the head without reducing under abstractions. Terms are compiled to a de Bruijn notation in which consecutive abstractions are grouped into a single $\lambda_n$ and a variable is a pair $\langle \nu, k\rangle$: the $k$-th variable of the $\lambda$-block $\nu$ levels up.

- **Environments and closures.** An environment is either empty or a finite sequence $(e, \varphi_1, \dots, \varphi_n)$, where $e$ is an environment and the $\varphi_i$ are closures. A closure is a pair $(t, e)$ of a term and an environment, and a stack is a finite sequence of closures.
- **States and steps.** A state is a triple $(t, e, \pi)$, and a step leads to the next state $(t', e', \pi')$:
    - if $t = (u)v$, then $t' = u$, $e' = e$ and $\pi' = (v, e).\pi$: push the argument closure;
    - if $t = \lambda_n u$ and the stack has at least $n$ entries $\varphi_1 \dots \varphi_n.\pi'$, then $t' = u$ and $e' = (e, \varphi_1, \dots, \varphi_n)$; otherwise the machine stops;
    - if $t = \langle \nu, k\rangle$, follow $\nu$ parent links from $e$ to $e_\nu = (e_{\nu+1}, (t_1, \varepsilon_1), \dots, (t_p, \varepsilon_p))$. If $k \le p$, continue with $t' = t_k$, $e' = \varepsilon_k$ and $\pi' = \pi$. The machine stops if an environment on the way is empty or $k > p$.
- **The value of a closure.** Each closure $(t, e)$ has a value $t[e]$, a closed term: substitute the values of the closures provided by $e$ for the free variables of $t$, and a fixed dummy constant where $e$ provides nothing. For a stack $\pi = (\varphi_1, \dots, \varphi_m)$ write $t[e]\bar\pi$ for $t[e]\,\bar\varphi_1 \cdots \bar\varphi_m$.

**Theorem.** If $(t, e, \pi)$ and $(t', e', \pi')$ are consecutive states of the machine, then $t[e]\bar\pi$ reduces to $t'[e']\bar\pi'$ by weak head reduction, in zero steps for the application and variable rules and in one step for the abstraction rule.

Consequently the machine computes weak head reduction correctly. If a closed term $t$ weak-head reduces to $a\,t_1 \cdots t_k$ with $a$ a constant, then running the compiled form of $t$ from the empty environment and the empty stack ends in $a$ applied to the compiled $t_1, \dots, t_k$.

## Sources

- J.-L. Krivine, "A call-by-name lambda-calculus machine", *Higher-Order and Symbolic Computation* 20(3):199–207, 2007, <https://www.irif.fr/~krivine/articles/lazymach.pdf>, Section 2: weak head reduction, closures, environments and stacks, the execution rules, the value of a closure, and Theorem 3 with the correctness remark that follows it.
