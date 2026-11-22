# Cauchy–Schwarz step for Gowers powers

Let $G$ be a finite abelian group and let $\mathbb{E}$ denote an average over $G$. For every $d \ge 0$ and $f : G \to \mathbb{C}$, the number $\|f\|_{U^{d+1}}^{2^{d+1}}$ is real and

$$\bigl|\,\|f\|_{U^d}^{2^d}\bigr|^2 \le \|f\|_{U^{d+1}}^{2^{d+1}}.$$

The proof is by induction on $d$ from the recursion (1.1): $|\mathbb{E}_h a_h|^2 \le \mathbb{E}_h |a_h|^2$ applied to $a_h = \|\Delta_h f\|_{U^{d-1}}^{2^{d-1}}$. It is the argument behind Green and Tao's monotonicity (1.2), and gives both [positivity](gowers-pow-succ-re-nonneg.md) and [monotonicity](gowers-norm-le-gowers-norm-succ.md).

## Sources

- B. Green and T. Tao, "An inverse theorem for the Gowers $U^3(G)$ norm", Proc. Edinb. Math. Soc. 51 (2008), 73–153; numbering of arXiv:math/0503014, (1.1) and (1.2).
