# Fisher information operator

For densities $p_\theta$ with respect to $\nu$ indexed by a finite-dimensional real inner product space $E$, with score $s_\theta$, the Fisher information operator is

$$I(\theta) = \int s_\theta\,s_\theta^\top\,dP_\theta, \qquad P_\theta = p_\theta\,\nu,$$

the Bochner integral of the rank-one operators $v \mapsto \langle s_\theta, v\rangle s_\theta$ ($0$ if the score is not square integrable). When $s_\theta$ is square integrable under $P_\theta$, its quadratic form is $\langle I(\theta)u, u\rangle = \int\langle s_\theta, u\rangle^2dP_\theta$.
