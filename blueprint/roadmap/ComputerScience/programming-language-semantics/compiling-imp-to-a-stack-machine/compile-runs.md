# Compiled command code simulates big-step execution

Let $c$ be a command and $s$, $s'$
states such that $c$ run from $s$ terminates in $s'$ under the big-step semantics. Let $P$ and
$Q$ be lists of instructions, $\sigma$ a stack, $|P|$ the length of $P$, $C_p(c)$ the compiled
code of $c$ at base program counter $p$, and $\ell(c)$ the instruction count of $c$. Then the
stack machine running the program $P \, C_{|P|}(c) \, Q$ (the concatenation of $P$,
$C_{|P|}(c)$ and $Q$) goes in finitely many steps from program counter $|P|$, stack $\sigma$ and
state $s$ to program counter $|P| + \ell(c)$, the same stack $\sigma$ and state $s'$.
