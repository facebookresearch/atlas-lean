# Expected volume of a random simplex in a convex body

For $d \in \mathbb{N}$ and a set $K \subseteq \mathbb{R}^d$, the expected simplex volume of $K$ is

$$\mathbb{E} V_d(P^K_{d+1}) = \frac{1}{|K|^{d+1}} \int_{K^{d+1}} \bigl|\operatorname{conv}\{x_0, \dots, x_d\}\bigr| \, dx_0 \cdots dx_d,$$

where $|\cdot|$ is Lebesgue measure on $\mathbb{R}^d$ (taken as a real number, an infinite measure counting as $0$) and the integral is over $(x_0, \dots, x_d) \in K^{d+1}$ with the product Lebesgue measure. When $K$ is measurable with $0 < |K| < \infty$ and the volume of the convex hull is integrable over $K^{d+1}$, for instance when $K$ is a convex body, this is the expected volume of the convex hull of $d + 1$ independent points uniform in $K$. Finite measure alone is not enough: a set of finite measure can make that integral diverge, and the value is then $0$. Division by $0$ gives $0$, and a non-integrable integrand gives integral $0$.
