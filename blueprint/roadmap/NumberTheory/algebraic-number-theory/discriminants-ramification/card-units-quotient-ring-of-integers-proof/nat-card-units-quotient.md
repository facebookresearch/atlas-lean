# Number of units of the ring of integers modulo an ideal

Let $S$ be a Dedekind domain
that is a finite free $\mathbb{Z}$-module, for example the ring of integers $\mathcal{O}_K$ of a
number field $K$, and for a nonzero ideal $\mathfrak{b}$ let
$N(\mathfrak{b}) = \#(S/\mathfrak{b})$ be its absolute norm (`Ideal.absNorm`). If
$\mathfrak{a} \neq 0$ is an ideal of $S$, then the unit group of the finite ring
$S/\mathfrak{a}$ has

$$\#\bigl((S/\mathfrak{a})^\times\bigr) = N(\mathfrak{a}) \prod_{\mathfrak{p} \mid \mathfrak{a}}
\left(1 - \frac{1}{N(\mathfrak{p})}\right)$$

elements, as an identity of rational numbers. The product runs over the finite set
`(normalizedFactors 𝔞).toFinset` of the distinct prime factors of $\mathfrak{a}$, which by
`Ideal.mem_normalizedFactors_iff` are exactly the prime ideals of $S$ containing $\mathfrak{a}$.

This is F. Keune, *Number Fields*, Radboud University Press (2023), Chapter 6, Exercise 1(iii)
(p. 142), stated there for $\mathcal{O}_K$; the ring here is any Dedekind domain that is a finite
free $\mathbb{Z}$-module. For $S = \mathbb{Z}$ and $\mathfrak{a} = n\mathbb{Z}$ it is Euler's
product formula for $\varphi(n)$.
