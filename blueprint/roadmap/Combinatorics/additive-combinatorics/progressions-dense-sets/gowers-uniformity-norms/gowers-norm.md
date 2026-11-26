# Gowers uniformity norm

Let $G$ be a finite abelian group and $f : G \to \mathbb{C}$. For $d \ge 0$, $\|f\|_{U^d} = |\,\|f\|_{U^d}^{2^d}|^{1/2^d}$, the $2^d$-th root of the modulus of the [$2^d$-th power](gowers-pow.md). For $d \ge 1$ this is the $U^d(G)$ norm of Green and Tao (Definition 1.6). Gowers's original $\|f\|_d$ uses sums instead of averages, so it is $|G|^{(d+1)/2^d}$ times this one. For $d = 0$ the definition gives $|\mathbb{E} f|$, the modulus of Green and Tao's complex number $\|f\|_{U^0} = \mathbb{E} f$.

$U^1$ is in general only a seminorm (when $|G| > 1$), since [$\|f\|_{U^1} = |\mathbb{E} f|$](gowers-norm-one.md); for $d \ge 2$, $U^d$ is a norm (Gowers, Lemma 3.9; [triangle inequality](gowers-norm-add-le.md)). For $f = e(\varphi)$ the norm measures how far the $d$-th derivative of the phase is from vanishing: it is $1$ when $\varphi$ is a polynomial of degree less than $d$.

## Sources

- B. Green and T. Tao, "An inverse theorem for the Gowers $U^3(G)$ norm", Proc. Edinb. Math. Soc. 51 (2008), 73–153; numbering of arXiv:math/0503014, Definition 1.6, (1.1) and the remarks after it.
- William Timothy Gowers, "A new proof of Szemerédi's theorem", Geom. Funct. Anal. 11 (2001), 465–588, Lemma 3.9.
