# Gowers uniformity norm, raised to the power $2^d$

For $f : G \to \mathbb{C}$ on a finite abelian group, the quantity $\|f\|_{U^d}^{2^d}$ is defined by the recursion

$$\|f\|_{U^0} = \mathbb{E}_x f(x), \qquad \|f\|_{U^{d+1}}^{2^{d+1}} = \mathbb{E}_{h \in G} \|\Delta_h f\|_{U^d}^{2^d},$$

where $\Delta_h$ is the [multiplicative derivative](mul-deriv.md). This is formula (1.1) of Green and Tao, who state it as equivalent to their Definition 1.6, the average over cubes $\mathbb{E}_{x, h_1, \dots, h_d} \prod_{\omega \in \{0,1\}^d} C^{|\omega|} f(x + \omega \cdot h)$; the equivalence is the [cube formula](gowers-pow-eq-cube-average.md). For $d \ge 1$ the value is a [nonnegative real number](gowers-pow-succ-re-nonneg.md); for $d = 0$ it is the complex mean of $f$.

## Sources

- B. Green and T. Tao, "An inverse theorem for the Gowers $U^3(G)$ norm", Proc. Edinb. Math. Soc. 51 (2008), 73–153; numbering of arXiv:math/0503014, Definition 1.6 and (1.1).
