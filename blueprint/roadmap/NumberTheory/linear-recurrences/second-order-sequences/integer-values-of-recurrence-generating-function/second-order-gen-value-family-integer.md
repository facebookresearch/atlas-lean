# Integer values propagate along a family

Let $a, b, p$ be integers with $p \ne 0$, let
$A(x) = \frac{a(1 - px) + bx}{1 - px - x^2}$ for rational $x$, and for integers $r, s$ let
$A^{(r,s)}$ be the two-sided integer sequence with $A^{(r,s)}_0 = r$, $A^{(r,s)}_1 = s$ and
$A^{(r,s)}_{n+2} = pA^{(r,s)}_{n+1} + A^{(r,s)}_n$ for all integers $n$. If $r$ and $s$ are
coprime integers with $s \ne 0$ and $A(r/s)$ is an integer, then
$A(A^{(r,s)}_n / A^{(r,s)}_{n+1})$ is an integer for every integer $n$ with
$A^{(r,s)}_{n+1} \ne 0$.

## Sources

- Luu Ba Thang and Nguyen Duy Nguyen, *Integer Values of Generating Functions for a Type of Second-Order Linear Recurrence Sequence*, Journal of Integer Sequences 28 (2025), Article 25.8.3, Theorem 1 (`jis-2025-25.8.3-thm-1`).
