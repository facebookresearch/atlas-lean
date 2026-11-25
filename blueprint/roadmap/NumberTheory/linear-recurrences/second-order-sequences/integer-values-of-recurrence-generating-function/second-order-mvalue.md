# The quantity $M(r, s)$ for the recurrence $A_{n+1} = pA_n + A_{n-1}$

For integers $a$,
$b$, $p$, $r$, $s$, $M(r, s) = \frac{br^2 + bs^2 - apr^2 + 2ars}{s^2 - prs - r^2}$, a rational
number, with the convention that a fraction with denominator $0$ is $0$.

When $s \ne 0$ and $s^2 - prs - r^2 \ne 0$, write $k = A(r/s)$, where
$A(x) = \frac{a(1 - px) + bx}{1 - px - x^2}$ is the generating function of the sequence with
$A_0 = a$, $A_1 = b$ and $A_{n+1} = pA_n + A_{n-1}$; then
$M(r, s)^2 = (kp + b - ap)^2 - 4k(a - k)$, that is,
$M(r, s) = \pm\sqrt{(kp + b - ap)^2 - 4k(a - k)}$.

## Sources

- Luu Ba Thang and Nguyen Duy Nguyen, *Integer Values of Generating Functions for a Type of Second-Order Linear Recurrence Sequence*, Journal of Integer Sequences 28 (2025), Article 25.8.3, Section 2 (before Lemma 8).
