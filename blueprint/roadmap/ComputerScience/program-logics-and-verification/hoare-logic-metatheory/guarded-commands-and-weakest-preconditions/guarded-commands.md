# Guarded commands

Let a set of *basic statements*, such as $\mathbf{skip}$ and assignments $x := E$ of expressions to variables, be given. A *guarded command* is a pair $B \to SL$ of a Boolean expression $B$, its *guard*, and a nonempty *guarded list* $SL$ of statements separated by semicolons. Statements are the basic statements and the two constructs built from a nonempty finite set $B_1 \to SL_1 \mathbin{[\!]} \cdots \mathbin{[\!]} B_n \to SL_n$ of guarded commands:

- the *alternative construct* $\mathbf{if}\ B_1 \to SL_1 \mathbin{[\!]} \cdots \mathbin{[\!]} B_n \to SL_n\ \mathbf{fi}$, and
- the *repetitive construct* $\mathbf{do}\ B_1 \to SL_1 \mathbin{[\!]} \cdots \mathbin{[\!]} B_n \to SL_n\ \mathbf{od}$.

Write $BB$ for $B_1 \vee \dots \vee B_n$. A guarded list is executed from left to right, and it may be selected for execution only in a state in which its guard is true; the order in which the guarded commands are written is irrelevant. The alternative construct *aborts* if no guard is true in the initial state, and otherwise executes one guarded list whose guard is true, chosen arbitrarily, so the construct may be nondeterministic. The repetitive construct terminates properly in a state in which no guard is true; otherwise it selects and executes a guarded list whose guard is true, and repeats. When it terminates properly, all its guards are false. For example, $\mathbf{if}\ x \ge y \to m := x \mathbin{[\!]} y \ge x \to m := y\ \mathbf{fi}$ sets $m$ to the maximum of $x$ and $y$.

## Sources

- E. W. Dijkstra, "Guarded commands, nondeterminacy and formal derivation of programs", *Communications of the ACM* 18(8):453–457, 1975; author's manuscript EWD472, <https://www.cs.utexas.edu/~EWD/ewd04xx/EWD472.PDF>, Section 2.
