# Lower chain

Let $\Bbbk$ be a field with a linear order. The lower chain of a list of
points $p_1, \dots, p_n$ of $\Bbbk^2$ is computed by Andrew's monotone chain scan: start with an
empty stack and process $p_1, \dots, p_n$ in order; for each point $p = p_i$, remove the top $a$
of the stack as long as the stack has a second element $b$ with
$(a_x - b_x)(p_y - b_y) - (p_x - b_x)(a_y - b_y) \le 0$, then push $p$. The lower chain is the
final stack read from bottom to top. Each evaluation of the inequality costs one unit; nothing
else is counted.

The scan is meant for points sorted strictly in lexicographic $(x, y)$ order; the chain then runs
from left to right.
