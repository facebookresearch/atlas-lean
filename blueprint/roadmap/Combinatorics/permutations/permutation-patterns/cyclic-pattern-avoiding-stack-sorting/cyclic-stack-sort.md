# Cyclic-pattern-avoiding stack-sorting map

For a finite sequence $\sigma$ of natural
numbers, the map $s_{[\sigma]}$ sends a finite sequence $\pi$ of natural numbers to the output of
the following procedure. Read $\pi$ from left to right, starting with an empty stack. Before
pushing the next entry $x$, pop the fewest entries from the top of the stack such that the stack
with $x$ pushed on top, read from top to bottom, contains no rotation of $\sigma$ as a pattern (if
even the stack holding only $x$ contains one, the whole stack is popped and $x$ is pushed anyway);
popped entries are appended to the output in the order they are removed. Once $\pi$ is exhausted,
the remaining stack is appended to the output from top to bottom. Here a sequence $w$ contains
$p = p_1 \cdots p_m$ as a pattern when some subsequence $w_1' \cdots w_m'$ of $w$ satisfies
$w_i' < w_j' \iff p_i < p_j$ for all $1 \le i, j \le m$.

## Sources

- Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026), Article A15, Section 1.
