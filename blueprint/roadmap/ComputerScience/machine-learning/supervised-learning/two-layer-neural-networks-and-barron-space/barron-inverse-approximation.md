# Inverse approximation theorem for the Barron space

Let $f$ be continuous on the cube $[0, 1]^d$ and let $Q \in \mathbb{R}$. Suppose that two-layer
ReLU networks $f_k(x) = \frac{1}{w_k} \sum_{i=1}^{w_k} a_i \max(\langle b_i, x \rangle + c_i, 0)$
of widths $w_k \ge 1$, each with path norm
$\frac{1}{w_k} \sum_i \lvert a_i \rvert (\lVert b_i \rVert_1 + \lvert c_i \rvert) \le Q$, converge
to $f$ at every point of the cube. Then $f$ admits a Barron representation on the cube, and
$\lVert f \rVert_B \le Q$.

Together with the [direct approximation theorem](barron-direct-approximation.md), this
characterizes the Barron space as the set of functions approximable by two-layer networks with
bounded path norm. Proof in the source: after normalizing $\lVert b \rVert_1 + \lvert c \rvert = 1$
by homogeneity of the ReLU, each $f_k$ is represented by a probability measure supported in the
compact set $\{\lvert a \rvert \le Q, \lVert b \rVert_1 + \lvert c \rvert \le 1\}$; Prokhorov's
theorem gives a weakly convergent subsequence, whose limit represents $f$.

## Background

- [Convergence of measures](../../../../Probability/convergence-of-measures/README.md): tightness and Prokhorov's theorem, used in the source's proof in the parameter space $\mathbb{R} \times \mathbb{R}^d \times \mathbb{R}$.

## Sources

- W. E, C. Ma and L. Wu, *The Barron space and the flow-induced function spaces for neural network models*, Constr. Approx. 55 (2022), Theorem 5 and its proof in §2.5.4.
