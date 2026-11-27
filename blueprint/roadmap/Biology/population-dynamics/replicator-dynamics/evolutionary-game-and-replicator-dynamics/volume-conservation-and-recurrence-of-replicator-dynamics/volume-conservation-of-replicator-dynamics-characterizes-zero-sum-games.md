# Volume conservation of replicator dynamics characterizes zero-sum games

**Setting.** A graphical polymatrix game has players $i \in V$, each with actions $\{1, \dots, n_i\}$ and mixed strategies $x_i$ in the simplex $\Delta^{n_i - 1}$, and a bimatrix game $(A^{i,j}, A^{j,i})$ on every edge of a directed graph that may contain self-loops; the payoff of action $\alpha$ is $u_{i,\alpha}(x) = \sum_j (A^{i,j} x_j)_\alpha$ and $u_i(x) = x_i \cdot \sum_j A^{i,j} x_j$. A one-population evolutionary game with payoff matrix $A$ is the case of a single player with a self-loop. The game is zero-sum when the block matrix $A$ is antisymmetric; the self-loop ("diagonal") game of player $i$ is zero-sum when $A^{i,i}$ is antisymmetric. The replicator dynamics are

$$\dot x_{i,\alpha} = x_{i,\alpha}\bigl(u_{i,\alpha}(x) - u_i(x)\bigr).$$

On the interior, the map $\mathbf f : x_i \mapsto \bigl(\ln(x_{i,2}/x_{i,1}), \dots, \ln(x_{i,n_i}/x_{i,1})\bigr)$ is a diffeomorphism onto **cumulative-payoff space** $\prod_i \mathbb{R}^{n_i - 1}$; the conjugate flow $\psi^t = \mathbf f \circ \phi^t \circ \mathbf f^{-1}$ solves $\dot y_{i,\alpha} = u_{i,\alpha+1} - u_{i,1}$ evaluated at $\mathbf f^{-1}(y)$.

Two matrices define the same replicator vector field when they differ by a matrix with constant columns, $\mathbf 1 (c_1, \dots, c_n)$; call a diagonal game *equivalent to zero-sum* if it is antisymmetric up to such a term.

**Theorem 2.** If every diagonal game is zero-sum, the flow $\psi$ in cumulative-payoff space preserves Lebesgue volume.

**Theorem 3.** For a one-population game with matrix $A$, if $\psi$ preserves volume at every point of some nonempty open set, then $A = B + \mathbf 1\,(A_{11}, \dots, A_{nn})$ with $B$ antisymmetric, so the game is equivalent to a zero-sum game.

**Theorem 4.** A polymatrix game with self-loops is volume conservative in cumulative-payoff space if and only if each of its diagonal games is equivalent to a zero-sum game. In particular, volume conservation on an open set forces volume conservation everywhere.

## Expansion

By Liouville's formula volume is conserved iff the divergence of the vector field vanishes. In cumulative-payoff space the divergence is $\sum_{i,\alpha} \partial \dot y_{i,\alpha}/\partial y_{i,\alpha}$, and a player's own coordinates enter its payoffs only through its self-loop game, so only the diagonal games contribute; for a one-population game the divergence is the polynomial

$$\sum_\alpha x_\alpha A_{\alpha\alpha} - \sum_{\alpha,\beta} x_\alpha x_\beta A_{\alpha\beta},$$

which is identically zero for antisymmetric $A$. Conversely, a polynomial vanishing on an open set vanishes identically; eliminating $x_n = 1 - \sum_{\alpha<n} x_\alpha$, the coefficient of $x_\alpha^2$ is $A_{\alpha\alpha} + A_{nn} - A_{\alpha n} - A_{n\alpha}$, and its vanishing for all pairs is exactly the decomposition $A = B + \mathbf 1\,(A_{11}, \dots, A_{nn})$. Volume conservation rules out any asymptotically stable interior rest point, since volume would have to shrink near it.

## Depends on

- [Solution of the replicator equation](../../is-solution.md)

## Sources

- V. Boone, G. Piliouras, "From Darwin to Poincaré and von Neumann: recurrence and cycles in evolutionary and algorithmic game theory" (2019), Section 3 (Theorems 2, 3 and 4) and Appendix A (divergence formula, Lemma 7), <https://doi.org/10.48550/arXiv.1910.01334>.
