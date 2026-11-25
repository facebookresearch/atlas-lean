# Continuous mapping theorem on the real line

Let $\mu_n$ ($n \in \mathbb{N}$) and $\mu$ be probability measures on $\mathbb{R}$ such that $\mu_n$ converges weakly to $\mu$, and let $g : \mathbb{R} \to \mathbb{R}$ be a measurable function whose set $D_g$ of discontinuity points satisfies $\mu(D_g) = 0$. Then the image measures $\mu_n \circ g^{-1}$ converge weakly to $\mu \circ g^{-1}$: if $\int f \, d\mu_n \to \int f \, d\mu$ for every bounded continuous $f : \mathbb{R} \to \mathbb{R}$, then $\int f \, d(\mu_n \circ g^{-1}) \to \int f \, d(\mu \circ g^{-1})$ for every such $f$. The case of a continuous $g$ is the special case $D_g = \emptyset$.

## Idea

In the language of random variables: if $X_n$ converges in distribution to $X$, then $g(X_n)$ converges in distribution to $g(X)$ whenever $g$ is continuous at almost every value of $X$. Discontinuities are allowed where the limit puts no mass. For example, if $X_n$ converges in distribution to a standard normal $Z$, then $X_n^2$ converges to the chi-square law with one degree of freedom, and $1/X_n$ converges to $1/Z$ whatever value $1/0$ is given, because $Z = 0$ has probability zero. One proof uses the portmanteau theorem: for a closed set $F$, the closure of $g^{-1}(F)$ lies in $g^{-1}(F) \cup D_g$, so $\limsup_n \mu_n(g^{-1}(F)) \le \mu(g^{-1}(F))$.

## Statements

- [Continuous mapping theorem for weak convergence of probability measures](tendsto-map-of-tendsto-of-ae-continuous.md)
- [Continuous mapping theorem, integral form](continuous-mapping.md): integral form
