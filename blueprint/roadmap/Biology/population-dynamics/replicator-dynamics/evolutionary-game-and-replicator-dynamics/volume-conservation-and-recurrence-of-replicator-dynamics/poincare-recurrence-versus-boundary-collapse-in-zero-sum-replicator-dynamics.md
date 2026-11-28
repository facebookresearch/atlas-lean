# Poincaré recurrence versus boundary collapse in zero-sum replicator dynamics

**Setting.** Replicator dynamics $\dot x_{i,\alpha} = x_{i,\alpha}(u_{i,\alpha}(x) - u_i(x))$ of a graphical polymatrix game with self-loops whose payoff block matrix is antisymmetric (zero-sum), as in [volume conservation of replicator dynamics](volume-conservation-of-replicator-dynamics-characterizes-zero-sum-games.md). A flow is *Poincaré recurrent* if for every open set almost every orbit meeting it returns to it infinitely often. For distributions $p, q$ on the same action set, $\mathrm{KL}(p \,\|\, q) = \sum_\alpha p_\alpha \ln(p_\alpha/q_\alpha)$.

**Theorem 5 (recurrence).** If a zero-sum polymatrix game with self-loops has an interior (fully mixed) Nash equilibrium $x^*$, then the replicator dynamics are Poincaré recurrent on the interior. The key facts are Lemma 1, that $\sum_i \mathrm{KL}(x_i^* \,\|\, x_i)$ is a constant of motion, and Lemma 2, that every interior orbit stays bounded away from the boundary.

**Theorem 6 (boundary collapse; attributed in the source to Akin, 1984).** For a one-population zero-sum game (antisymmetric $A$) with no interior Nash equilibrium, let $x^*$ be a Nash equilibrium of maximal support. Then $\frac{d}{dt}\mathrm{KL}(x^* \,\|\, x) < 0$ along interior orbits (Lemma 3), and every interior orbit collapses to the boundary: every $y \in \omega(x)$ satisfies $\operatorname{supp} y \subseteq \operatorname{supp} x^*$.

**Theorem 7 (dichotomy for evolutionary games).** For a one-population matrix game $A$ under replicator dynamics, volume is preserved in cumulative-payoff space iff $A = B + \mathbf 1\,(A_{11}, \dots, A_{nn})$ with $B$ antisymmetric. In that case interior orbits are Poincaré recurrent iff there is an interior Nash equilibrium; otherwise every interior orbit collapses to the face spanned by the support of a maximal-support Nash equilibrium.

**Theorem 9 (periodicity with three strategies).** For a one-population zero-sum game with $n = 3$ strategies and an interior Nash equilibrium, every interior non-equilibrium point lies on a periodic orbit.

On the collapsed face both convergence and boundary cycling occur. For Rock-Paper-Scissors with a dominated fourth strategy,

$$A = \begin{pmatrix} 0 & -1 & 1 & 10 \\ 1 & 0 & -1 & 10 \\ -1 & 1 & 0 & 10 \\ -10 & -10 & -10 & 0 \end{pmatrix},$$

the unique Nash equilibrium is $(\tfrac13, \tfrac13, \tfrac13, 0)$; the source reports that the orbit from $(\tfrac14, \tfrac14, \tfrac14, \tfrac14)$ converges to it while the orbit from $(\tfrac{3}{16}, \tfrac{5}{16}, \tfrac14, \tfrac14)$ approaches a periodic orbit on the face $x_4 = 0$.

## Expansion

With an interior equilibrium $x^*$, $\frac{d}{dt}\sum_i \mathrm{KL}(x_i^* \| x_i) = -\sum_i (x_i^* - x_i)\cdot \sum_j A^{i,j} x_j$, and antisymmetry together with the equalizing property of an interior equilibrium makes this zero. Level sets of the KL sum are compact in the interior, so orbits are bounded in cumulative-payoff space; volume conservation plus bounded orbits gives Poincaré recurrence, which transfers back through the diffeomorphism. Without an interior equilibrium, the one-population game is embedded as the invariant diagonal of the two-player game with matrices $(A, -A^{\mathsf T})$; that game has no interior equilibrium either (equilibrium strategies are maxmin strategies, the same for both players), and the known two-player strict decrease of the KL sum restricts to the diagonal. A strict Lyapunov function forces $\omega$-limits into the face of the maximal-support equilibrium. Recurrence near the barycenter would contradict collapse, giving the converse in Theorem 7. With three strategies the interior is two-dimensional, the KL level sets are closed curves avoiding the rest point, and the Poincaré-Bendixson theorem gives periodicity.

## Depends on

- [Volume conservation of replicator dynamics characterizes zero-sum games](volume-conservation-of-replicator-dynamics-characterizes-zero-sum-games.md)
- [Solution of the replicator equation](../../is-solution.md)

## Sources

- V. Boone, G. Piliouras, "From Darwin to Poincaré and von Neumann: recurrence and cycles in evolutionary and algorithmic game theory" (2019), Section 4 (Theorems 5, 6 and 7, Lemmas 1-4) and the section on cycles in dimension 3 (Lemmas 5 and 6, Theorem 9, Proposition 1), <https://doi.org/10.48550/arXiv.1910.01334>.
