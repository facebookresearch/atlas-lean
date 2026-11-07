# Baker–Wüstholz theorem on linear forms in logarithms

Let $n \ge 1$, let $K$ be a number
field of degree $d = [K : \mathbb{Q}]$, let $\varphi : K \to \mathbb{C}$ be a ring homomorphism,
and let $\alpha_1, \dots, \alpha_n$ be nonzero elements of $K$. Let $b_1, \dots, b_n$ be integers
and let $B \ge 2$ be a natural number with $|b_i| \le B$ for every $i$. With $\log$ the principal
branch of the complex logarithm, suppose that $\Lambda = \sum_{i=1}^n b_i \log \varphi(\alpha_i)$
is nonzero. Then

$$\log |\Lambda| \ge -C(n, d) \max\left(\log B, \frac{1}{d}\right) \prod_{i=1}^n h'(\alpha_i),$$

where $C(n, d)$ is the Baker–Wüstholz constant and $h'$ is the modified height with respect to
$\varphi$.

## Sources

- A. Baker, G. Wüstholz, Logarithmic forms and group varieties, J. reine angew. Math. 442 (1993), 19-62. Via leanprover/lean-eval@38361be, problem `bakerWustholz_linearForms_logs`.
