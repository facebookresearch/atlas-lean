# Explicit count of Pell solutions in a closed rotated square

Let $D$ be an integer and let
$(\alpha, \beta)$ be a fundamental solution of $x^2 - Dy^2 = 1$, that is, an integer solution
with $\alpha > 1$ and $\beta > 0$ such that $\alpha \le x$ for every integer solution $(x, y)$ with
$x > 1$ (one exists only when $D$ is positive and not a square). For $n \ge 0$ let $u_n, v_n$ be
the integers with $u_n + v_n\sqrt D = (\alpha + \beta\sqrt D)^n$. For real $\lambda$ let
$Q(\lambda)$ be the set of integer pairs $(x, y)$ with $x^2 - Dy^2 = 1$ and
$|x| + |y| \le \lambda$. If $\lambda < 1$, then $Q(\lambda)$ is empty. If $\lambda \ge 1$, let
$m = \left\lfloor \left(\log\lfloor\lambda\rfloor + \log\frac{2\sqrt D}{1 + \sqrt D}\right) /
\log(\alpha + \beta\sqrt D) \right\rfloor$; then $Q(\lambda)$ consists of the pairs
$(i\,u_n, j\,v_n)$ with $i, j \in \{1, -1\}$ and integers $0 \le n \le m$, and $Q(\lambda)$ has
exactly $2 + 4m$ elements.

## Sources

- Kun Yi Ong and Eddie Shahril Bin Ismail, *Integer Solutions of Pell Equation in a Closed Rotated Square Region*, INTEGERS 25 (2025), Article A112, Corollary 2.4 (`integers-2025-A112-cor-2-4`).
