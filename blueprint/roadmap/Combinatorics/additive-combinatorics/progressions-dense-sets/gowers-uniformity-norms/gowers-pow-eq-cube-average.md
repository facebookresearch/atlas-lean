# Gowers norms as cube averages

Let $G$ be a finite abelian group and let $\mathbb{E}$ denote an average over $G$. For every $d \ge 0$ and $f : G \to \mathbb{C}$, the [$2^d$-th power](gowers-pow.md) $P_d(f)$, written $\|f\|_{U^d}^{2^d}$ by Green and Tao, satisfies

$$P_d(f) = \mathbb{E}_{x \in G,\ h \in G^d} \prod_{\omega \in \{0,1\}^d} C^{|\omega|} f(x + \omega \cdot h),$$

where $C$ is complex conjugation, $|\omega|$ is the number of coordinates of $\omega$ equal to $1$ and $\omega \cdot h = \sum_i \omega_i h_i$. For $d \ge 1$, $P_d(f)$ is a nonnegative real number, the $2^d$-th power of the real [Gowers norm](gowers-norm.md) $\|f\|_{U^d}$; for $d = 0$ the identity reads $P_0(f) = \mathbb{E} f$, a complex number whose modulus is $\|f\|_{U^0}$. This is Definition 1.6 of Green and Tao; with the [recursive definition](gowers-pow.md) it proves their remark that (1.1) is an equivalent definition. The configurations $(x + \omega \cdot h)_\omega$ are the cubes of dimension $d$, so $P_d(1_A)$ is the number of cubes in $A$ divided by $|G|^{d+1}$.

## Sources

- B. Green and T. Tao, "An inverse theorem for the Gowers $U^3(G)$ norm", Proc. Edinb. Math. Soc. 51 (2008), 73–153; numbering of arXiv:math/0503014, Definition 1.6 and (1.1).
- William Timothy Gowers, "A new proof of Szemerédi's theorem", Geom. Funct. Anal. 11 (2001), 465–588, §3 (cubes and Lemma 3.7).
