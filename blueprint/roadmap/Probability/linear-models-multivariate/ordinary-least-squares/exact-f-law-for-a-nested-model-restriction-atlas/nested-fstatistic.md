# F statistic for nested linear models

Let $X$ be a real $n \times p$ unrestricted design and $X_0$ a real $n \times p_0$ restricted design, and let $y \in \mathbb{R}^n$. With $\mathrm{RSS}_U = \|y - X\hat\beta\|^2$ and $\mathrm{RSS}_R = \|y - X_0\hat\gamma\|^2$ the residual sums of squares of the least-squares fits of $y$ on $X$ and on $X_0$ (where the inverse of a singular Gram matrix is taken to be zero), the nested-model statistic is

$$F = \frac{(\mathrm{RSS}_R - \mathrm{RSS}_U)/(p - p_0)}{\mathrm{RSS}_U/(n - p)},$$

where $p - p_0$ and $n - p$ are truncated at $0$ and a quotient by $0$ is $0$.
