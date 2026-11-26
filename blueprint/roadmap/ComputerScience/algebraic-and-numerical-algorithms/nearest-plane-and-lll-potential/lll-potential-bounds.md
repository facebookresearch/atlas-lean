# Bounds on the LLL potential and the number of exchanges

Size-reduction steps preserve the integer span, linear independence, all Gram-Schmidt vectors and hence $D$; an exchange step at $i$ preserves the span and multiplies $d_i$, hence $D$, by a factor less than $\delta$. If the $b_i$ have integral inner products then $D \ge 1$, and if $\|b_i\|^2 \le B$ for all $i$ then $D \le B^{n(n-1)/2}$. Consequently, for $0 < \delta < 1$, the LLL algorithm performs at most $\log_{1/\delta}\big(B^{n(n-1)/2}\big)$ exchange steps on an integer basis, a number polynomial in $n$ and $\log B$ for fixed $\delta$.

## Proof sketch

Each $d_i$ is the squared volume of the first $i$ vectors and is a positive integer for integral Gram matrices; Hadamard's inequality gives the upper bound. Only $d_i$ changes under an exchange at $i$, by the factor $\|b_{i+1}^* + \mu b_i^*\|^2/\|b_i^*\|^2 < \delta$.

## Depends on

- [The LLL potential](lll-potential.md)

## Sources

- A. K. Lenstra, H. W. Lenstra Jr. and L. Lovász, "Factoring Polynomials with Rational Coefficients", Mathematische Annalen 261(4), 1982.
