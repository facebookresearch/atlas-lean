# Asymptotic enumeration of k-noncrossing RNA structures with arc length at least 3

**Definitions.** For an integer $k \ge 3$, a **$k$-noncrossing RNA structure with arc-length $\ge 3$** on $[n]=\{1,\dots,n\}$ is a diagram of arcs $(i,j)$, $i<j$, with every vertex in at most one arc, no arc of the form $(i,i+1)$ or $(i,i+2)$, and no set of $k$ mutually crossing arcs (arcs $(i_1,j_1),\dots,(i_k,j_k)$ with $i_1<\dots<i_k<j_1<\dots<j_k$). Let $\mathsf S_{k,3}(n)$ be their number, and let $f_k(2n,0)$ be the number of $k$-noncrossing perfect matchings on $[2n]$; let $r_k$ be the radius of convergence of $\sum_{n\ge0} f_k(2n,0)z^{2n}$. The case $k=2$ recovers secondary structures; $k=3$ allows pseudoknots with at most two mutually crossing helices.

**Functional equation (Lemma 2).** As formal power series (and as analytic functions for $|z|$ below the radius of convergence, Lemma 3),

$$
\sum_{n \ge 0}\mathsf S_{k,3}(n)\,z^n = \frac{1}{1-z+z^2+z^3-z^4}\sum_{n \ge 0} f_k(2n,0)\left(\frac{z-z^3}{1-z+z^2+z^3-z^4}\right)^{2n}.
$$

**Theorem (exponential growth, Theorem 2).** Let

$$
\vartheta(z) = \frac{z(1-z)(1+z)}{-\left(z^2-\tfrac12\right)^2 + z\left(z^2-\tfrac12\right) - \tfrac z2 + \tfrac54}, \qquad z \in \left[0,\tfrac{\sqrt2}{2}\right].
$$

Then $\sum_n \mathsf S_{k,3}(n)z^n$ has a unique real dominant singularity $\rho_k$, the unique real solution of $\vartheta(\rho_k)=r_k$, and $\mathsf S_{k,3}(n)$ grows with exponential rate $1/\rho_k$, i.e. $\lim_{n\to\infty}\mathsf S_{k,3}(n)^{1/n} = 1/\rho_k$.

**Theorem (3-noncrossing case, Theorem 4).** For $k=3$,

$$
\mathsf S_{3,3}(n) \sim \frac{6.11170\cdot 4!}{n(n-1)\cdots(n-4)}\;4.54920^n, \qquad n\to\infty,
$$

so the subexponential factor is of order $n^{-5}$, in contrast with $n^{-3/2}$ for secondary structures.

## Expansion

Inclusion–exclusion over arcs of length $1$ and $2$ (Theorem 1 of the source) expresses $\mathsf S_{k,3}(n)$ through numbers of $k$-noncrossing partial matchings; summing gives the functional equation, a composition of the matching generating function with the rational map $z \mapsto (z-z^3)/(1-z+z^2+z^3-z^4)$. The dominant singularity of the composite is reached where the inner map hits the singularity $r_k$ of the matching series, which gives $\vartheta(\rho_k)=r_k$. For $k=3$, $f_3(2n,0) = C_nC_{n+2}-C_{n+1}^2$ (Catalan numbers) has a D-finite generating function whose singular expansion at $r_3$ contains a term $(1-z/r_3)^4\ln(1-z/r_3)$; composing and applying the logarithmic transfer theorem (Theorem 3 of the source) with $r=4$ gives the factor $4!/(n(n-1)\cdots(n-4))$.

## Sources

- E. Y. Jin and C. M. Reidys, "Pseudoknot RNA structures with arc-length $\ge 3$", arXiv:0708.3134 (2007), Section 2 (Theorem 1, Lemmas 1–3), Section 3 (Theorem 2) and Section 4 (Theorems 3–4), <https://doi.org/10.48550/arXiv.0708.3134>.
