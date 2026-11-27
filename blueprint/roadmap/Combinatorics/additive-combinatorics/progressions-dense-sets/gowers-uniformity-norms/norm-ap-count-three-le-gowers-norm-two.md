# Generalized von Neumann theorem for three-term progressions

Let $G$ be a finite abelian group, let $\mathbb{E}$ denote an average over $G$, let  $|G|$ be odd and let $f_0, f_1, f_2 : G \to \mathbb{C}$ take values in the closed unit disc. Then

$$|\Lambda_3(f_0, f_1, f_2)| \le \|f_j\|_{U^2} \quad (j = 0, 1, 2).$$

This is the case $k = 3$ of Green and Tao's Proposition 1.7 and of Gowers's Theorem 3.2. The proof is Roth's Fourier argument: by the [Fourier expansion of $\Lambda_3$](card-pow-three-mul-ap-count-three.md), Cauchy–Schwarz, Parseval and $\|\hat f\|_\infty \le \|\hat f\|_4 = \|f\|_{U^2}$; oddness makes $\psi \mapsto \psi^{-2}$ a bijection of the dual group. The [same bound for every $k$](norm-ap-count-le-gowers-norm.md) follows from Green and Tao's Cauchy–Schwarz argument instead.

## Background

- [Bounds for Roth numbers](../bounds-for-roth-numbers/README.md): Roth's theorem, whose density-increment proof starts from this bound and the [$U^2$ inverse theorem](exists-character-correlation-of-le-gower.md).

## Sources

- B. Green and T. Tao, "An inverse theorem for the Gowers $U^3(G)$ norm", Proc. Edinb. Math. Soc. 51 (2008), 73–153; numbering of arXiv:math/0503014, Proposition 1.7.
- William Timothy Gowers, "A new proof of Szemerédi's theorem", Geom. Funct. Anal. 11 (2001), 465–588, Theorem 3.2.
