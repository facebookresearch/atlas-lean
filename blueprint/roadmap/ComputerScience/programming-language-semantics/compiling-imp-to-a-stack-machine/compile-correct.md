# Correctness of compilation to the stack machine

Let $c$ be a command and $s$, $s'$ states
such that $c$ run from $s$ terminates in $s'$ under the big-step semantics. Let $C_0(c)$ be the
compiled code of $c$ at base program counter $0$ and $\ell(c)$ the instruction count of $c$.
Then the stack machine running $C_0(c)$ goes in finitely many steps from program counter $0$,
the empty stack and state $s$ to program counter $\ell(c)$, the empty stack and state $s'$.

Since $C_0(c)$ has exactly $\ell(c)$ instructions, no step is possible at program counter
$\ell(c)$, so the machine halts there. Only this forward simulation is claimed, not its
converse.
