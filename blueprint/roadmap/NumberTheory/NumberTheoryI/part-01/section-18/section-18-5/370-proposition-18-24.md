---
article_id: af_e1da5b56bee57ac21f9c9dc4
declaration: theorem
origin: cited
lean: RiemannStieltjes.integration_by_parts
---

# Proposition 18.24

Let $f, g$, and $h$ be functions on $[a, b]$ and let $c_1$ and $c_2$ be constants. The following hold: (1) If $f, g \in S(h)$ then $\int_a^b (c_1 f + c_2 g)\,dh = c_1 \int_a^b f\,dh + c_2 \int_a^b g\,dh$. (2) If $f \in S(g), S(h)$ then $\int_a^b f\,d(c_1 g + c_2 h) = c_1 \int_a^b f\,dg + c_2 \int_a^b f\,dh$. (3) If $f \in S(g)$ then for any $c \in [a, b]$ we have $\int_a^b f\,dg = \int_a^c f\,dg + \int_c^b f\,dg$. (4) If $f \in S(g)$ then $g \in S(f)$ and $\int_a^b f\,dg + \int_a^b g\,df = f(b)g(b) - f(a)g(a)$. (5) If $f = f_1 + if_2$ and $g = g_1 + ig_2$ with $f_1, f_2 \in S(g_1), S(g_2)$ then $\int_a^b f\,dg = \left(\int_a^b f_1\,dg_1 - \int_a^b f_2\,dg_2\right) + i\left(\int_a^b f_2\,dg_1 + \int_a^b f_1\,dg_2\right)$.

## Depends on

- [Definition 18.23](369-definition-18-23.md)

## Sources

- [MIT 18.785 Number Theory I (Fall 2021), Section 18.5](../../../../../../sources/v1/NumberTheoryI.md)
