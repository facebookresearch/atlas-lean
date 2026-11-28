# Asymptotic stability of the pre-mRNA–mRNA–protein switching PDMP

**Model.** A gene switches between an inactive state $\gamma=0$ and an active state $\gamma=1$. Activation occurs at rate $q_0(x)$ and inactivation at rate $q_1(x)$, where the rates may depend on the current levels $x=(x_1,x_2,x_3)$ of pre-mRNA, mRNA and protein, for example through protein feedback. Between switches the levels evolve deterministically:

$$\dot x_1=A_1\gamma(t)-d_1x_1,\qquad \dot x_2=A_2x_1-d_2x_2,\qquad \dot x_3=A_3x_2-d_3x_3 .$$

After rescaling this becomes the piecewise-deterministic Markov process (PDMP)

$$\dot x_1=\gamma(t)-x_1,\qquad \dot x_2=a(x_1-x_2),\qquad \dot x_3=b(x_2-x_3),\qquad a,b>0,$$

on $[0,1]^3\times\{0,1\}$. Its densities evolve under a Markov semigroup $\{P(t)\}$ on $L^1$. With constant rates, the mean levels are $\mathbb E x_1=\frac{A_1q_0}{d_1(q_0+q_1)}$, $\mathbb Ex_2=\frac{A_2}{d_2}\mathbb Ex_1$ and $\mathbb Ex_3=\frac{A_3}{d_3}\mathbb Ex_2$. In the adiabatic limit $q_0,q_1\to\infty$ with fixed ratio, $\gamma$ is replaced by $q_0/(q_0+q_1)$.

**Theorem.** Assume $q_0,q_1>0$ on $[0,1]^3$ and $a\ne b$, $a\ne1$, $b\ne1$ (the conclusion also holds without these inequalities). Then $\{P(t)\}$ is asymptotically stable: there is a unique invariant density $f^*$, and $\|P(t)f-f^*\|_{L^1}\to0$ for every initial density $f$. The support of $f^*$ is $\mathbb A=A\times\{0,1\}$. Here $A\subset[0,1]^3$ is the region bounded by two surfaces: the active-state trajectories issuing from the inactive-state trajectory $\phi$ from $(1,1,1)$ to $0$, and the inactive-state trajectories issuing from the active-state trajectory $\psi$ from $0$ to $(1,1,1)$. Write $x$ in the eigenbasis $v_1,v_2,v_3$ of the linear vector field, with eigenvalues $-1,-a,-b$, normalized so that $(1,1,1)$ has coordinates $(1,1,1)$. Then

$$A=\{(x-y+z,\ x^a-y^a+z^a,\ x^b-y^b+z^b):\ 1\ge x\ge y\ge z\ge0\}.$$

The set $\mathbb A$ is invariant, attracts every trajectory, and is minimal with these two properties. Its two-dimensional projections reproduce the attractor of the planar mRNA–protein model. With suitable negative feedback, however, the three-stage system can display limit-cycle-like oscillations that are impossible in the planar model.

## Expansion

In each gene state the flow is linear, $\dot x=Mx+\gamma e_1$, with $M$ lower triangular with eigenvalues $-1,-a,-b$. In the eigenbasis a trajectory started at a point with coordinates $(u_1,u_2,u_3)$ has coordinates $(u_1e^{-t},u_2e^{-at},u_3e^{-bt})$, relative to the target $0$ or $(1,1,1)$. With $x=e^{-t_1}$, $y=e^{-t_2}$, $z=e^{-t_3}$, the boundary surfaces of $A$ are images of switch sequences inactive→active→inactive, which yields the parametrization above. Asymptotic stability follows a general criterion for Markov semigroups of PDMPs on compact spaces. If (a) $\int_0^\infty P(t)f\,dt>0$ a.e. for every density, and (b) every point has a neighbourhood from which the semigroup dominates a nontrivial integral kernel, then the semigroup is either asymptotically stable or sweeping. On a compact space sweeping is impossible. Condition (b) is verified by a Hörmander-type bracket condition: $g_1-g_0$ and the Lie brackets of the two vector fields span $\mathbb R^3$, which makes the cumulative-flow map a submersion. Condition (a) follows because every point of $A$ communicates with every other.

These are the theorem of Section 3.1 and the appendices (attractor formula and proof of asymptotic stability) of the source.

## Sources

- R. Rudnicki, A. Tomski, "On a stochastic gene expression with pre-mRNA, mRNA and protein contribution", arXiv:1505.06147 (2015). <https://doi.org/10.48550/arXiv.1505.06147>
