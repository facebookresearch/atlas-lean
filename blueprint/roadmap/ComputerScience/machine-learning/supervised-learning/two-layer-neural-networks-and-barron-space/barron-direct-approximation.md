# Direct approximation theorem for the Barron space

Let $f$ have finite Barron norm $\lVert f \rVert_B$, let $\mu$ be a probability measure carried
by the cube $[0, 1]^d$, and let $m \ge 1$. Then there are neuron parameters
$(a_k, b_k, c_k) \in \mathbb{R} \times \mathbb{R}^d \times \mathbb{R}$, $k = 1, \dots, m$, such
that the two-layer network $f_m(x) = \frac1m \sum_{k=1}^m a_k \max(\langle b_k, x \rangle + c_k, 0)$
satisfies

$$\lVert f - f_m \rVert_{L^2(\mu)}^2 \le \frac{3 \lVert f \rVert_B^2}{m}
\qquad\text{and}\qquad
\frac1m \sum_{k=1}^m \lvert a_k \rvert (\lVert b_k \rVert_1 + \lvert c_k \rvert) \le 2 \lVert f \rVert_B.$$

The rate $m^{-1/2}$ is the Monte Carlo rate and does not depend on $d$, and the path norm of the
approximant is controlled independently of the width.

Proof (as in the source, with one simplification): take a representation $\rho$ of $f$ whose
second moment $M_2 = \mathbb{E}_\rho[a^2 (\lVert b \rVert_1 + \lvert c \rvert)^2]$ is below
$1.21 \lVert f \rVert_B^2$, and sample the $m$ neurons i.i.d. from $\rho$. For each $x$ in the cube
the expected squared error is the variance of an i.i.d. sample mean, at most $M_2 / m$, and
Tonelli's theorem integrates this over $\mu$; the expected path norm is
$\mathbb{E}_\rho \lvert a \rvert (\lVert b \rVert_1 + \lvert c \rvert) \le \sqrt{M_2}$ by
Cauchy–Schwarz. The source applies Markov's inequality to the two quantities separately; this
proof instead averages the single functional
$\mathrm{error} / (3 \lVert f \rVert_B^2 / m) + \mathrm{path\ norm} / (2 \lVert f \rVert_B)$,
whose mean is below $1.21/3 + 1.1/2 < 1$, so that some sample makes it smaller than $1$. A function
of Barron norm $0$ vanishes on the cube and is approximated by the zero network.

## Informally uses

- [Variance of the sample mean of i.i.d. samples](../../../../Probability/laws-of-large-numbers/variance-sample-mean-of-iid.md): the pointwise Monte Carlo computation $\mathbb{E}_\Theta \lvert f_m(x) - f(x) \rvert^2 \le \mathbb{E}_\rho \lvert a \sigma(\langle b, x \rangle + c) \rvert^2 / m$.

## Sources

- W. E, C. Ma and L. Wu, *The Barron space and the flow-induced function spaces for neural network models*, Constr. Approx. 55 (2022), Theorem 4 and its proof in §2.5.3.
- W. E, C. Ma and L. Wu, *A priori estimates of the population risk for two-layer neural networks*, Commun. Math. Sci. 17 (2019), Theorem 3.1 (the analogous statement for networks without bias on $[-1, 1]^d$, without the factor $1/m$).
