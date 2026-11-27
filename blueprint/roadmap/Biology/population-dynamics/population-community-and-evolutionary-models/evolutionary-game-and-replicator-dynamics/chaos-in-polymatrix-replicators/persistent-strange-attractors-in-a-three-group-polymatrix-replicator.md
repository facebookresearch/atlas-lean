# Persistent strange attractors in a three-group polymatrix replicator

**Polymatrix replicator.** A population is divided into groups $\alpha = 1, 2, 3$; individuals of each group use one of two strategies, with frequencies $x^\alpha = (x_1^\alpha, x_2^\alpha)$, $x_1^\alpha + x_2^\alpha = 1$. The block payoff matrix $P = (P^{\alpha,\beta})$ records in $p^{\alpha,\beta}_{i,j}$ the payoff to a group-$\alpha$ individual playing $i$ against a group-$\beta$ individual playing $j$, and

$$\dot x_i^\alpha = x_i^\alpha\Bigl((Px)_i^\alpha - \sum_{j=1}^{2} x_j^\alpha (Px)_j^\alpha\Bigr), \qquad (Px)_i^\alpha = \sum_{\beta}\sum_k p^{\alpha,\beta}_{i,k} x_k^\beta .$$

For two strategies per group this reduces to $\dot x_1^\alpha = x_1^\alpha(1 - x_1^\alpha)\bigl((Px)_1^\alpha - (Px)_2^\alpha\bigr)$ (Lemma 1); the phase space $\Delta^1 \times \Delta^1 \times \Delta^1$ is identified with the cube $[0,1]^3$, which is flow-invariant, as are its faces (Lemma 2).

**The family.** For the payoff matrix chosen in the source (with second rows of each group normalized to zero, which leaves the vector field unchanged), writing $x = x_2^1$, $y = x_2^2$, $z = x_2^3$, the dynamics become the one-parameter family $f_\mu$:

$$\begin{aligned} \dot x &= x(1-x)\bigl(12 - \mu + (\mu - 14)x - 20y - 4z\bigr),\\ \dot y &= y(1-y)\bigl(-10 + 20x + 4y - 4z\bigr),\\ \dot z &= z(1-z)\bigl(27 - 54x + 11y - 4z\bigr). \end{aligned}$$

**Lemma 4 (interior equilibrium).** For $\mu \in (-\tfrac{2938}{95}, 10)$ the system has a unique interior equilibrium

$$\mathcal O_\mu = \Bigl(\frac{7\mu - 1042}{7\mu - 2014},\ \frac{37(\mu - 10)}{7\mu - 2014},\ \frac{109(\mu - 10)}{2(7\mu - 2014)}\Bigr).$$

**Lemma 5.** There are parameters $\mu_1 < \mu_2 < \mu_4$ in this range at which $\mathcal O_\mu$ undergoes a Belyakov transition ($\mu_1$) and supercritical Hopf bifurcations ($\mu_2$ and $\mu_4$).

**Theorem A (persistent strange attractors).** There is a parameter interval $I$ such that for every $\tilde\mu \in I$ and every $C^2$ neighbourhood $\mathcal U$ of $f_{\tilde\mu}$ among $C^2$ vector fields leaving $[0,1]^3$ invariant, there is a generic one-parameter family $(g_\lambda)_{\lambda \in [-1,1]} \subset \mathcal U$ exhibiting strange attractors for a set of parameters $\lambda$ of positive Lebesgue measure. Here a strange attractor of a vector field means a Hénon-type strange attractor of a first-return map: the closure of the unstable manifold of a hyperbolic periodic point, with a basin of positive measure and a dense orbit with a positive Lyapunov exponent.

**Status of the proof.** The argument rests on properties checked numerically in the source (Facts 1-5): on $I$ the largest Lyapunov exponent of $f_\mu$ is positive; the eigenvalues of $Df_\mu(\mathcal O_\mu)$ are $\lambda_u \pm i\omega$ and $-\lambda_s$ with $\lambda_u, \omega, \lambda_s > 0$ and $2\lambda_u < \lambda_s$; and a $C^2$-close vector field has a homoclinic orbit to the continuation of $\mathcal O_\mu$. Theorem A is proved assuming these facts.

## Expansion

After time reversal the homoclinic orbit to the saddle-focus satisfies Shilnikov's eigenvalue condition, so the first-return map to a cross section has an invariant set conjugate to a full shift on infinitely many symbols, containing a sequence of heteroclinically related horseshoes. Unfolding the homoclinic orbit generically in a parameter $\lambda$ breaks the orbit but leaves finitely many horseshoes, and homoclinic tangencies to dissipative periodic points are dense in the parameter interval (Newhouse, Ovsyannikov-Shilnikov). Near each such tangency the return map is a small perturbation of the Hénon family, and the Mora-Viana theory of Hénon-like families gives strange attractors for a positive-measure set of parameters. Phenomenologically, the route to chaos starts with an attracting limit cycle born in a supercritical Hopf bifurcation of $\mathcal O_\mu$; as $\mu$ varies this cycle winds around the focus and accumulates on the stable manifold of the interior equilibrium, through successive saddle-node and period-doubling bifurcations, until the homoclinic configuration is reached.

## Depends on

- [Solution of the replicator equation](../../../replicator-dynamics/is-solution.md)

## Sources

- T. Peixe, A. A. Rodrigues, "Persistent strange attractors in 3D polymatrix replicators" (2021), Section 2 (model, Lemmas 1 and 2), Section 3 (Theorem A), Section 4 (Lemmas 3-5), Section 5 (numerical Facts 1-5) and Section 7 (proof of Theorem A), <https://doi.org/10.48550/arXiv.2103.11242>.
