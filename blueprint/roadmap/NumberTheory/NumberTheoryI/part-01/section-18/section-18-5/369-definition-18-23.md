---
article_id: af_4502e3408d5ef573fa5a7140
declaration: def
origin: cited
statement: formalized
lean: RiemannStieltjes.StieltjesIntegrable
---

# Definition 18.23

Let $f$ and $g$ be (real or complex valued) functions defined on a nonempty real interval $[a, b]$. For any partition $P=(x_0, \ldots, x_n)$ of $[a, b]$ and sequence $T=(t_1, \ldots, t_n)$ with $t_k \in [x_{k-1}, x_k]$, we define the Riemann-Stieltjes sum $$S(P, T, f, g)\coloneqq \sum_{k=1}^{n} f(t_k)(g(x_k)-g(x_{k-1})).$$ We say that $f$ is Riemann-Stieltjes integrable with respect to $g$ and write $f \in S(g)$ if there is a (real or complex) number $S$ such that for every $\epsilon>0$ there is a partition $P_{\epsilon}$ of $[a, b]$ such that for every refinement $P=(x_0, \ldots, x_n)$ of $P_{\epsilon}$ and every sequence $T=(t_1, \ldots, t_n)$ with $t_k \in [x_{k-1}, x_k]$ we have $|S(P, T, f, g)-S|\lt \epsilon$. When such an $S$ exists it is necessarily unique and we denote it by $\int_a^b f\, dg$, the Riemann-Stieltjes integral of $f$ with respect to $g$. Improper Riemann-Stieltjes integrals are then defined as limits $\int_a^{\infty} f\, dg\coloneqq \lim_{b \rightarrow \infty} \int_a^b f\, dg$ (and similarly for the lower limit), and we define $\int_b^a f\, dg=-\int_a^b f\, dg$ and $\int_a^a f\, dg=0$.

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.785 Number Theory I (Fall 2021), Section 18.5](../../../../../../sources/v1/NumberTheoryI.md)
