# Three-point identity for Bregman divergences

Throughout, $E$ is a real normed space with norm $\|\cdot\|$, linear forms $\xi \in E^*$ (continuous linear maps $E \to \mathbb{R}$) carry the dual norm $\|\xi\|_* = \sup_{\|x\| \le 1} \xi(x)$, $\omega \colon E \to \mathbb{R}$ is a distance-generating function with a derivative selection $\omega' \colon E \to E^*$, and $V_x(u)$ is its Bregman divergence. For all $x, y, u \in E$,

$$
V_x(u) - V_y(u) - V_x(y) = \big(\omega'(y) - \omega'(x)\big)(u - y).
$$

Both sides expand to $\omega'(y)(u - y) - \omega'(x)(u - y)$. This rearrangement turns the first-order optimality condition of a prox step into a telescoping inequality, and it is the only algebra behind the mirror descent and mirror-prox bounds.

## Sources

- A. Juditsky and A. Nemirovski, *First order methods for nonsmooth convex large-scale optimization, I: general purpose methods*, in S. Sra, S. Nowozin and S. J. Wright (eds.), *Optimization for Machine Learning*, MIT Press (2011); author PDF at <https://www2.isye.gatech.edu/~nemirovs/MLOptChapterI.pdf>, Section 5.2.3, the rearrangement (5.12) in the proof of Proposition 5.1.
