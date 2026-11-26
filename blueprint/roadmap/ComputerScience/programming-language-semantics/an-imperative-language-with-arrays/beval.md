# Truth of Boolean expressions in the imperative language with arrays

The truth of a Boolean expression $b$ in a state $s$ is the proposition $b(s)$ defined by recursion on $b$: the constant true is always true; the comparison $e_1 \le e_2$ is true when $e_1(s) \le e_2(s)$; the conjunction $b_1 \wedge b_2$ is true when both $b_1(s)$ and $b_2(s)$ are; and the negation $\neg b$ is true when $b(s)$ is not. Truth is a proposition, not a Boolean value.
