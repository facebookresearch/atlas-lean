# Algorithm for integer values of a second-order generating function

Let $a, b, p$ be
integers with $p \ne 0$ and $(a, b) \ne (0, 0)$, let $A(x) = \frac{a(1 - px) + bx}{1 - px - x^2}$
for rational $x$, and for integers $r, s$ let $A^{(r,s)}$ be the two-sided integer sequence with
$A^{(r,s)}_0 = r$, $A^{(r,s)}_1 = s$ and $A^{(r,s)}_{n+2} = pA^{(r,s)}_{n+1} + A^{(r,s)}_n$ for all
integers $n$. Put $E = abp^3 + (a^2 - b^2)p^2$, and let $B = E/(p^2 + 4)$ if $E \ge 0$ and
$B = -abp + b^2 - a^2$ if $E < 0$. (Soundness) If $M$ and $k$ are integers with $k \ne 0$ and
$M^2 = (kp - ap + b)^2 - 4k(a - k)$, then $A(x)$ is an integer for both
$x = (ap - kp - b + M)/(2k)$ and $x = (ap - kp - b - M)/(2k)$. (Completeness) If $x$ is a
rational number for which $A(x)$ is an integer, then at least one of the following holds: there
is an integer $n$ with $A^{(0,1)}_{n+1} \ne 0$ and $x = A^{(0,1)}_n / A^{(0,1)}_{n+1}$; there is
an integer $n$ with $A^{(-b,a)}_{n+1} \ne 0$ and $x = A^{(-b,a)}_n / A^{(-b,a)}_{n+1}$; or there
are integers $M, N, k$ with $M^2 \le B$, $M^2 + (p^2 + 2)MN + N^2 = E$, $k \ne 0$ and
$M^2 = (kp - ap + b)^2 - 4k(a - k)$, and a rational number
$x' \in \{(ap - kp - b + M)/(2k), (ap - kp - b - M)/(2k)\}$ such that $x$ lies in the family of
$x'$: writing $x' = u/v$ in lowest terms with $v > 0$, there is an integer $n$ with
$A^{(u,v)}_{n+1} \ne 0$ and $x = A^{(u,v)}_n / A^{(u,v)}_{n+1}$.

The bound $M^2 \le B$ is the condition $|M| \le \sqrt{B}$ of the source.

## Sources

- Luu Ba Thang and Nguyen Duy Nguyen, *Integer Values of Generating Functions for a Type of Second-Order Linear Recurrence Sequence*, Journal of Integer Sequences 28 (2025), Article 25.8.3, Theorem 3 (`jis-2025-25.8.3-thm-3`).
