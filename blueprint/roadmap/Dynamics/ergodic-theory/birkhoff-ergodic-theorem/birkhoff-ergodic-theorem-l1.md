# Birkhoff's ergodic theorem in $L^1$ (ergodic case)

Let $\mu$ be a probability measure
on a measurable space $\alpha$, let $T : \alpha \to \alpha$ be ergodic with respect to $\mu$ (in
particular $T$ preserves $\mu$), and let $g : \alpha \to \mathbb{R}$ be $\mu$-integrable. For
$n \ge 1$ let $A_n g(x) = \frac{1}{n} \sum_{k=0}^{n-1} g(T^k x)$ be the Birkhoff averages of
$g$. Then $\int \left| A_n g(x) - \int g \, d\mu \right| d\mu(x) \to 0$ as $n \to \infty$; that
is, the Birkhoff averages of $g$ converge to the constant $\int g \, d\mu$ in $L^1(\mu)$.
