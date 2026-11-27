# A small value of $M$ in the family of $r/s$ when $abp + a^2 - b^2 < 0$

Let $a, b, p$ be
integers with $p \ne 0$ and $abp + a^2 - b^2 < 0$. Let $A(x) = \frac{a(1 - px) + bx}{1 - px - x^2}$
for rational $x$, and for integers $u, v$ let
$M(u, v) = \frac{bu^2 + bv^2 - apu^2 + 2auv}{v^2 - puv - u^2}$, where in both a fraction with
denominator $0$ is read as $0$. Let $r, s$ be coprime integers with $s \ne 0$ such that $A(r/s)$
is an integer, and let $(A^{(r,s)}_n)_{n \in \mathbb{Z}}$ be the two-sided sequence with
$A^{(r,s)}_0 = r$, $A^{(r,s)}_1 = s$ and $A^{(r,s)}_{n+1} = pA^{(r,s)}_n + A^{(r,s)}_{n-1}$ for
every integer $n$. If $A^{(r,s)}_n \ne 0$ for every integer $n$, then there is an integer $n$
with $|M(A^{(r,s)}_n, A^{(r,s)}_{n+1})| \le \sqrt{b^2 - a^2 - abp}$.

The hypothesis that no term vanishes is the paper's assumption before Lemma 8 ("we can assume
that the conditions $r \ne 0, s \ne 0, r + ps \ne 0$ automatically hold"). Without it the paper's
claim fails: for $(a, b, p) = (-1, 8, -1)$ and $x = 0$, the members $A_n/A_{n+1}$ of the family
$A^{(0,1)}$ with $A_{n+1} \ne 0$ have $\min |M| = 8 > \sqrt{55}$.

## Sources

- Luu Ba Thang and Nguyen Duy Nguyen, *Integer Values of Generating Functions for a Type of Second-Order Linear Recurrence Sequence*, Journal of Integer Sequences 28 (2025), Article 25.8.3, Lemma 9 (`jis-2025-25.8.3-lem-9`).
