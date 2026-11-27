# Number of read starts covering a base of a linear genome

On a linear genome with bases $\{0, \dots, G-1\}$, reads of length $L \le G$ lie inside the
genome, so their start positions are $s \in \{0, \dots, G - L\}$, and the read starting at $s$
covers the base $x$ when $s \le x < s + L$. For every base $x$, the number of starts covering $x$
is

$$\min(x, G - L) + 1 - (x + 1 - L),$$

where $x + 1 - L$ is natural subtraction (it is $0$ when $x + 1 < L$): the starts covering $x$
are those from $\max(x + 1 - L, 0)$ to $\min(x, G - L)$. The outer subtraction never truncates.
For $L = 0$ no start covers $x$ and the count is $0$.
