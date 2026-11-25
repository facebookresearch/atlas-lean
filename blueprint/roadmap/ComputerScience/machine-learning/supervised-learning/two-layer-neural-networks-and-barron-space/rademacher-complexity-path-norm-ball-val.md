# Rademacher complexity of path-norm balls of two-layer ReLU networks

Let $d \ge 1$, let $x_1, \dots, x_n \in \mathbb{R}^d$ have every coordinate in $[-1, 1]$, and let
$Q \ge 0$. The set $A_Q \subseteq \mathbb{R}^n$ of value vectors $(f(x_1), \dots, f(x_n))$ of the
two-layer ReLU networks $f(x) = \sum_k a_k \max(\langle w_k, x \rangle, 0)$, of any width, with
path norm $\sum_k \lvert a_k \rvert \lVert w_k \rVert_1 \le Q$, has empirical Rademacher complexity

$$R(A_Q) = \frac1n \mathbb{E}_\sigma \sup_{a \in A_Q} \sum_i \sigma_i a_i \le 2 Q \sqrt{\frac{2 \log(2d)}{n}}.$$

The bound does not depend on the width of the networks, and depends on the dimension only through
$\log(2d)$. Proof: by positive homogeneity of the ReLU, each network is a combination of single
neurons with $\lVert u \rVert_1 \le 1$ with total weight at most $Q$, and the two signs of the
outer weights cost the factor $2$ (step 1); the contraction lemma removes the ReLU (step 2); a
linear functional over the $\ell^1$ unit ball is at most its largest value at the $2d$ vectors
$\pm e_j$ (step 3); and Massart's lemma bounds the complexity of these $2d$ vectors, each of
Euclidean norm at most $\sqrt n$ on the sample (step 4).

## Background

- [Rademacher average of a ball of linear predictors](../../generalization-bounds-and-concentration/rademacher-average-linear-ball-le.md): the Hilbert-space ($\ell^2$) analogue, dimension free with no logarithm; the path norm uses the $\ell^1$ geometry, which costs $\sqrt{\log(2d)}$.

## Sources

- W. E, C. Ma and L. Wu, *A priori estimates of the population risk for two-layer neural networks*, Commun. Math. Sci. 17 (2019), bound (5.1) (attributed there to Neyshabur, Tomioka and Srebro, COLT 2015), with data in $X = [-1, 1]^d$.
- The proof is that of Theorem 6 of W. E, C. Ma and L. Wu, *The Barron space and the flow-induced function spaces for neural network models*, Constr. Approx. 55 (2022), §2.5.5.
