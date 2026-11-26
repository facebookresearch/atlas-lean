# Zero padding one short of the full support aliases

Let $M, K \ge 2$ be natural numbers and $N = M + K - 2$. There are signals $x$ and $y$ of lengths $M$ and $K$ such that the [cyclic convolution](cyclic-convolution.md) of their [zero extensions to length $N$](zero-extend.md) differs at $0$ from their [linear convolution](linear-convolution.md):

$$\bigl(x^{(N)} \circledast y^{(N)}\bigr)(0) \ne (x * y)(0).$$

So the bound $N \ge M + K - 1$ in [zero padding to the full support](padded-cyclic-eq-linear.md) cannot be lowered by one.
