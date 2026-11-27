# Upper tail estimate for Wigner ensembles

There are absolute constants $C, c > 0$ with the following property. Let $(X_{ij})_{i \le j}$ be
independent real random variables with $\mathbb{E} X_{ij} = 0$ and $|X_{ij}| \le 1$, and for each
$n$ let $M_n$ be the $n \times n$ real symmetric matrix with entries $X_{\min(i,j)\,\max(i,j)}$.
Then for every $n$ and every $A \ge C$,

$$\mathbb{P}\big(\|M_n\| > A\sqrt{n}\big) \le C e^{-cAn},$$

where $\|M_n\|$ is the operator norm on Euclidean space. In particular $\|M_n\| = O(\sqrt{n})$
with overwhelming probability.

Tao's statement allows complex entries; this is the real case. The proof bounds $\|Mx\|$ for each
point $x$ of a $\frac{1}{2}$-net of the unit sphere and takes a union bound over the
$e^{O(n)}$ net points.

## Background

- [Concentration of the operator norm](op-norm-concentration-median.md): background; the upper
  tail locates $\|M_n\|$ at scale $\sqrt{n}$, concentration then gives $O(1)$ fluctuations.

## Sources

- T. Tao, *Topics in Random Matrix Theory*, Graduate Studies in Mathematics 132, American Mathematical Society, 2012, Corollary 2.3.6 (with Corollary 2.3.5 and Lemmas 2.3.1–2.3.4).
