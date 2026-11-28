# Iterates of the projected power method

For a matrix $C \in \mathbb{C}^{n \times n}$ and a starting vector $x_0 \in \mathbb{C}^n$, the iterates of the projected (generalized) power method are defined recursively by

$$x_{t+1} = P(C x_t), \qquad t \ge 0,$$

where $P(a)_k = a_k / \lvert a_k \rvert$ if $a_k \neq 0$ and $P(a)_k = 1$ if $a_k = 0$.
