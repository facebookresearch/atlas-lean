# Monotone chain scan

Let $\Bbbk$ be a field with a linear order. Given a stack $S$ of
points of $\Bbbk^2$, listed top first, and a list of points $p_1, \dots, p_n$ of $\Bbbk^2$, the
scan processes $p_1, \dots, p_n$ in order: for each point $p = p_i$ it removes the top $a$ of the
stack as long as the stack has a second element $b$ with
$(a_x - b_x)(p_y - b_y) - (p_x - b_x)(a_y - b_y) \le 0$, and then pushes $p$. Starting from $S$,
the result is the final stack, top first. Each evaluation of this inequality costs one unit;
nothing else is counted.
