# Linear-programming optimality certificate

Let $A$ be a real $m \times n$ matrix, $b \in \mathbb{R}^m$, $c \in \mathbb{R}^n$. Suppose $x \ge 0$ with $A x \le b$ and $y \ge 0$ with $A^{\mathsf T} y \ge c$ (componentwise), and $c^{\mathsf T} x = b^{\mathsf T} y$. Then $c^{\mathsf T} x' \le c^{\mathsf T} x$ for every $x' \ge 0$ with $A x' \le b$, and $b^{\mathsf T} y \le b^{\mathsf T} y'$ for every $y' \ge 0$ with $A^{\mathsf T} y' \ge c$.
