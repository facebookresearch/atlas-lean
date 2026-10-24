---
article_id: af_bfbf4f1c0f72550922d5049a
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Integration.change_of_variables
---

# Theorem (Change of Variables) (Fundamental Theorem of Calculus section) (1)

Let $\varphi:[a,b]\to [c,d]$ be continuously differentiable with $\varphi'>0$ on $[a,b]$, $\varphi(a) = c$, and $\varphi(b) = d$. Then, $\int_c^d f(u)\,du = \int_a^b f(\varphi(x))\varphi'(x)\,dx$.

## Depends on

- [Definition (Continuous Functions) (1)](../../part-01/continuous-functions/043-continuous-functions.md)
- [Definition (Section on Derivative)](../../part-01/section-on-derivative/050-definition.md)
- [Theorem (Riemann Integral) (The Riemann Integral section)](../the-riemann-integral/068-riemann-integral.md)

## Proof depends on

- [Theorem (Fundamental Theorem of Calculus) (Fundamental Theorem of Calculus section) (1)](078-fundamental-theorem-of-calculus.md)

## Sources

- [MIT 18.100A Real Analysis (Fall 2020), Fundamental Theorem of Calculus section](../../../../../sources/v1/RealAnalysis.md)
