# Compiled Boolean code pushes the truth value of the expression

Let $b$ be a Boolean
expression with compiled code $C(b)$ and instruction count $\ell(b)$, let $P$ and $Q$ be lists of
instructions, $\sigma$ a stack and $s$ a state, and write $|P|$ for the length of $P$. The stack
machine running the program $P \, C(b) \, Q$ (the concatenation of $P$, $C(b)$ and $Q$) goes in
finitely many steps from program counter $|P|$, stack $\sigma$ and state $s$ to program counter
$|P| + \ell(b)$, the stack obtained from $\sigma$ by pushing $1$ if $b$ evaluates to true in $s$
and $0$ otherwise, and the same state $s$.
