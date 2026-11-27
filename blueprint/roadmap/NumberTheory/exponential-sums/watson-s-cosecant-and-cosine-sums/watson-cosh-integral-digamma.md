# Digamma evaluation of a hyperbolic Laplace integral

Let $b > 0$ be a real number and let
$\alpha, \beta$ be complex numbers with $\operatorname{Re}(\alpha + b - \beta) > 0$ and
$\operatorname{Re}(\alpha + b + \beta) > 0$. Then the function
$x \mapsto e^{-\alpha x} \cosh(\beta x) / \cosh(bx)$ is integrable on $(0, \infty)$, and, writing
$\psi$ for the digamma function,

$$
\int_0^\infty \frac{e^{-\alpha x} \cosh(\beta x)}{\cosh(bx)} \, dx =
\frac{1}{4b} \Bigl[ \psi\bigl(\tfrac34 + \tfrac{\alpha+\beta}{4b}\bigr) -
\psi\bigl(\tfrac14 + \tfrac{\alpha-\beta}{4b}\bigr) +
\psi\bigl(\tfrac34 + \tfrac{\alpha-\beta}{4b}\bigr) -
\psi\bigl(\tfrac14 + \tfrac{\alpha+\beta}{4b}\bigr) \Bigr].
$$

The source prints only the condition $\operatorname{Re}(\alpha + b - \beta) > 0$; the condition
$\operatorname{Re}(\alpha + b + \beta) > 0$ is also needed, since the integrand is even in $\beta$.

## Sources

- Iaroslav V. Blagouchine, *On a Generalization of Watson’s Trigonometric Sum (On Dowker’s Sum of Order One Half)*, INTEGERS 25 (2025), Article A30, Lemma 1.
