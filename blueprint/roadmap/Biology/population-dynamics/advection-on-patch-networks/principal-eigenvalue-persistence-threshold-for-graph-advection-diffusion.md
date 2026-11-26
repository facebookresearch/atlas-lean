# Principal-eigenvalue persistence threshold for logistic growth with graph advection and diffusion

**Model.** Habitat patches are the nodes of a graph with environmental conditions $\Theta_i$ (e.g. temperature). The species density $\mathbf{u} = (u_i)$ evolves by
$$\frac{d\mathbf{u}}{dt} = \mathbf{F}(\mathbf{u},\Theta) - d\,L\,\mathbf{u} - \alpha\,A^{adv}(\Theta)\,\mathbf{u}, \qquad F_i(u_i,\Theta_i) = \gamma(\Theta_i)\,u_i(1 - u_i) - \delta u_i,$$
with diffusion rate $d$, graph Laplacian $L$, advection rate $\alpha$, and a climate-driven advection matrix built from directed edge velocities $v_{ij}$ (flow from $j$ toward better conditions),
$$(A^{adv}\mathbf{u})_i = \sum_{j\in\mathcal{N}(i)}(v_{ij} - v_{ji})\,u_j - \Big(\sum_{j\in\mathcal{N}(i)}(v_{ji} - v_{ij})\Big)u_i .$$

**Lemma.** The discrete advection operator conserves total mass and is in general asymmetric and non-normal.

**Theorem (global persistence).** Let $M(\Theta,d,\alpha) = R - dL - \alpha A^{adv}(\Theta)$ with $R = \operatorname{diag}(\gamma(\Theta_i) - \delta)$, and let $\lambda_1(\Theta,d,\alpha)$ be its principal eigenvalue. If $\lambda_1 < 0$, extinction $\mathbf{u} = 0$ is globally asymptotically stable; if $\lambda_1 > 0$, extinction is unstable and the population persists at a positive equilibrium $\mathbf{u}_*$ in every node. The persistence threshold is $\lambda_1(\Theta, d, \alpha) = 0$.

**Theorem (node-specific persistence under advection).** Without diffusion, with $\gamma_i = \gamma(\Theta_i)$ and $r_i = \gamma_i - \delta$, each node obeys
$$\dot u_i = u_i(r_i - \alpha) - \gamma_iu_i^2 + \alpha\sum_{j\to i}u_j .$$
If node $i$ receives positive equilibrium inflow, $\alpha\sum_{j\to i}u_j^* > 0$, it has a strictly positive equilibrium $u_i^* > 0$ even when its local growth rate is negative, $r_i < 0$ (a sink sustained by upstream sources).

## Depends on

## Expansion

The linearization at extinction is $\dot{\mathbf{u}} = M\mathbf{u}$, and $M$ is a Metzler matrix (off-diagonal entries come from diffusion and advection inflows) that is irreducible on a connected patch graph, so its principal eigenvalue is real with a positive eigenvector. The logistic nonlinearity is concave and subhomogeneous, which upgrades the local criterion to global statements by monotone-systems arguments: $\lambda_1 < 0$ forces decay, $\lambda_1 > 0$ gives a unique positive equilibrium attracting all nonzero data. At a single node, positive inflow turns the logistic equation into a quadratic with a positive constant term, which always has one positive root.

## Sources

- P. Roy Chowdhury and S. Raha, "A graph based advection framework for climate-driven species distribution", arXiv:2604.05423 (2026), Lemmas 2.1, 2.2 and Theorems 3.1, 3.2, <https://doi.org/10.48550/arXiv.2604.05423>.
