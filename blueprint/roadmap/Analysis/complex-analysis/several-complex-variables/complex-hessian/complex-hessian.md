# Complex Hessian

Let $u : \mathbb{C}^n \to \mathbb{R}$ and $z \in \mathbb{C}^n$, write
$e_1, \dots, e_n$ for the standard basis of $\mathbb{C}^n$, write $i$ for the imaginary unit, and
for $a, b \in \mathbb{C}^n$ write $D^2u(z)(a, b)$ for the real Hessian of $u$ at $z$. The complex
Hessian of $u$ at $z$ is the $n \times n$ complex matrix whose $(j, k)$ entry is

$$
u_{j\bar k}(z) = \frac{D^2u(z)(e_j, e_k) + D^2u(z)(i e_j, i e_k) +
i \left(D^2u(z)(e_j, i e_k) - D^2u(z)(i e_j, e_k)\right)}{4}.
$$

When $u$ is of class $C^2$, in real coordinates $z_j = x_j + i y_j$ this is
$\partial^2 u / \partial z_j \partial \bar z_k =
(u_{x_j x_k} + u_{y_j y_k} + i (u_{x_j y_k} - u_{y_j x_k})) / 4$.
