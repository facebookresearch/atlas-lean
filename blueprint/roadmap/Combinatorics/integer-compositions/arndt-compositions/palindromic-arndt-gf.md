# Palindromic Arndt generating function

A palindromic Arndt composition of $n$ with
$k \ge 1$ parts is a tuple $(\sigma_1, \dots, \sigma_k)$ of positive integers with sum $n$ such
that $\sigma_{2i-1} > \sigma_{2i}$ whenever $2i \le k$, and $\sigma_i = \sigma_{k+1-i}$ for all
$i$; its middle summand is $\sigma_{\lfloor k/2 \rfloor + 1}$. The generating function
$PA(x, y, z)$ is the formal power series in $x, y, z$ with rational coefficients whose coefficient
of $x^n y^k z^m$ is the number of palindromic Arndt compositions of $n$ with $k$ parts and middle
summand $m$.

## Sources

- Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer Sequences 28 (2025), Article 25.3.6, Section 3.2 (definition of `PA`).
