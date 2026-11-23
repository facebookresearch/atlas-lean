# Exponential specialization

Let $\mathbb{Q}[[x_1, x_2, \dots]]$ be the ring of formal
power series in the variables $x_1, x_2, \dots$ with rational coefficients: its elements are the
formal sums $f = \sum_\alpha c_\alpha x^\alpha$, where $\alpha = (\alpha_1, \alpha_2, \dots)$
runs over the sequences of nonnegative integers with only finitely many nonzero terms,
$c_\alpha \in \mathbb{Q}$ and $x^\alpha = x_1^{\alpha_1} x_2^{\alpha_2} \cdots$. For $m \ge 0$,
write $[x_1 \cdots x_m] f$ for the coefficient in $f$ of the monomial $x_1 x_2 \cdots x_m$; for
$m = 0$ this is the constant term of $f$. The exponential specialization of $f$ is the formal
power series in one variable $t$

$$\operatorname{ex}(f) = \sum_{m \ge 0} \frac{[x_1 \cdots x_m] f}{m!} \, t^m \in \mathbb{Q}[[t]].$$
