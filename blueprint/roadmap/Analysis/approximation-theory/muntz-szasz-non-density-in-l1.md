# Müntz–Szász theorem in $L^1[0,1]$: non-density for a convergent reciprocal series

Let $(\lambda_k)_{k\ge1}$ be distinct positive real numbers with

$$\sum_{k\ge1}\frac1{\lambda_k}<\infty .$$

Then the linear span of the monomials $x\mapsto x^{\lambda_k}$, $k\ge1$, is not dense in $L^1([0,1])$ with Lebesgue measure. Equivalently, there is $h\in L^\infty([0,1])$, not zero almost everywhere, with

$$\int_0^1x^{\lambda_k}h(x)\,dx=0\qquad\text{for every }k\ge1 .$$

For example, the exponents $\lambda_m=\binom m2$, $m\ge2$, qualify, since $\sum_{m\ge2}1/\binom m2=2$. The uniform-norm statement for integer exponents is the [Müntz–Szász theorem for integer exponents](muntz-szasz-nat.md); density in $L^1$ is weaker than density in $C([0,1])$, so the non-density here does not follow from it.

## Expansion

A proof page must establish the non-density, for instance by a Blaschke-product or Gram-determinant estimate bounding the $L^1$ distance from a fixed monomial $x^{\mu}$, $\mu\notin\{\lambda_k\}$, to the span of the $x^{\lambda_k}$ from below; and the equivalence with the annihilator form, from the Hahn–Banach theorem and the identification of the dual of $L^1([0,1])$ with $L^\infty([0,1])$.

## Sources

- P. Borwein and T. Erdélyi, "The full Müntz theorem in $C[0,1]$ and $L_1[0,1]$", *Journal of the London Mathematical Society* (2) 54 (1996), 102–110.
