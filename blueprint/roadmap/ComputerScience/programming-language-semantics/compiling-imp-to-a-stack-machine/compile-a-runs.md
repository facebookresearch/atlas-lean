# Compiled arithmetic code pushes the value of the expression

Let $a$ be an arithmetic
expression with compiled code $C(a)$ and instruction count $\ell(a)$, let $P$ and $Q$ be lists of
instructions, $\sigma$ a stack and $s$ a state, and write $|P|$ for the length of $P$. The stack
machine running the program $P \, C(a) \, Q$ (the concatenation of $P$, $C(a)$ and $Q$) goes in
finitely many steps from program counter $|P|$, stack $\sigma$ and state $s$ to program counter
$|P| + \ell(a)$, the stack obtained from $\sigma$ by pushing the value of $a$ in $s$, and the
same state $s$.
