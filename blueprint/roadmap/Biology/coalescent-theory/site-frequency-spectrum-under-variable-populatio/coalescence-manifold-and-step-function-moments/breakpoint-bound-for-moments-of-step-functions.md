# Breakpoint bound for moments of nonnegative step functions

**Setting.** For a finite set $A\subset\mathbb N$ let

$$M(A)=\overline{\Big\{\big(\textstyle\int_0^1x^a\,d\mu\big)_{a\in A}:\mu\text{ a nonnegative Borel measure on }[0,1]\Big\}}$$

be the moment cone, and for $k\in\mathbb N$ let $M_k(A)$ be the closure of the set of moment vectors $\big(\int_0^1x^af(x)\,dx\big)_{a\in A}$ of nonnegative step functions $f$ on $[0,1]$ with at most $k$ breakpoints (at most $k+1$ constant pieces). Let $M^{\uparrow}_k(A),M^{\downarrow}_k(A)$ and $M^{\uparrow}(A),M^{\downarrow}(A)$ be the analogues for nondecreasing, respectively nonincreasing, densities.

**Theorem.**

1. $M_k(A)=M(A)$ if and only if $k\ge|A|-1$.
2. All proper faces of $M(A)$ are simplicial.
3. $M^{\uparrow}_k(A)=M^{\uparrow}(A)$ and $M^{\downarrow}_k(A)=M^{\downarrow}(A)$ if and only if $k\ge\lfloor|A|/2\rfloor$.
4. $M(A)$, $M^{\uparrow}(A)$ and $M^{\downarrow}(A)$ are linear projections of the spectrahedron $M(\{0,1,\dots,\max A\})$, so membership and nearest-point problems are semidefinite programs.

Thus, up to closure, any $|A|$ prescribed moments of a nonnegative measure are matched by a step density with $|A|-1$ breakpoints, and this is tight.

## Depends on

## Proof depends on

## Expansion

Shifting exponents does not change the cone, $M(A)=M(\{a-\min A:a\in A\})$, so one may assume $0\in A$; then $M(A)$ is the conical hull of the moment curve $t\mapsto(t^a)_{a\in A}$ on $[0,1]$ and is dual to the polynomials supported on $A$ that are nonnegative on $[0,1]$. A boundary point is the moment vector of a measure supported on the zeros of a nonnegative polynomial with support $A$; positivity of the generalized Vandermonde determinants $\det\big(r_j^{a_i}\big)$ for $0\le r_1<\dots<r_n\le1$ shows that distinct points of the moment curve are linearly independent, so every proper face is simplicial. A step function with $k$ breakpoints can approximate any measure with few atoms, which gives the upper bound. Conversely the step-function moments meet the boundary of $M(A)$ in a set of dimension at most $k$, while the boundary has dimension $|A|-1$, so fewer breakpoints cannot fill the cone. For monotone densities the cone is the conical hull of the moments of normalized indicator functions of $(t,1]$ (nondecreasing case) or $[0,t]$ (nonincreasing case), which halves the count.

## Sources

- Z. Rosen, G. Scholten, C. Vinzant, "Sparse moments of univariate step functions and allele frequency spectra", arXiv:2012.14467 (2020), Lemma 1.2, Theorem 1.5, Propositions 1.6 and 1.8, Corollary 1.9, Lemma 1.11, Corollary 1.12, Lemma 2.3, Propositions 2.4 and 2.5, Corollary 4.2, <https://doi.org/10.48550/arXiv.2012.14467>; published in *Vietnam Journal of Mathematics* 50(2) (2022) 523–544, <https://doi.org/10.1007/s10013-022-00548-5>. Locators follow arXiv v1.
