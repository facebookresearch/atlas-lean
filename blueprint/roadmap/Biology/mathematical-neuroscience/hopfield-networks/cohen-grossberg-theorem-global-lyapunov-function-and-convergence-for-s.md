# Cohen–Grossberg Lyapunov function for competitive networks

Cohen and Grossberg (1983) study competitive systems

$$\dot x_i = a_i(x_i)\Bigl[b_i(x_i) - \sum_{k=1}^n c_{ik}\, d_k(x_k)\Bigr], \qquad i = 1, \dots, n \qquad \text{(Eq. (1))},$$

with a symmetric matrix $C = (c_{ik})$; additive and shunting neural networks and Volterra–Lotka systems are special cases (Section I). They show (Section III) that

$$V(x) = -\sum_{i=1}^n \int_0^{x_i} b_i(\xi)\, d_i'(\xi)\, d\xi + \tfrac12 \sum_{j,k=1}^n c_{jk}\, d_j(x_j)\, d_k(x_k)$$

is a global Lyapunov function, because along solutions

$$\dot V = -\sum_{i=1}^n a_i(x_i)\, d_i'(x_i)\Bigl[b_i(x_i) - \sum_{k=1}^n c_{ik} d_k(x_k)\Bigr]^2,$$

which is $\le 0$ as long as every $a_i \ge 0$ and every $d_i$ is monotone nondecreasing; since $\partial V/\partial x_i = -d_i'(x_i)\bigl[b_i(x_i) - \sum_k c_{ik} d_k(x_k)\bigr]$, if every $d_i$ is differentiable with $d_i' > 0$ the system can be written in gradient form $\dot x = A(x)\nabla B(x)$ with $B = -V$ and $A(x) = \operatorname{diag}(a_i(x_i)/d_i'(x_i))$. Strict increase of $d_i$ alone does not suffice for this representation: for $n = 1$, $a = b = 1$, $C = 0$ and $d(x) = x^3$, the gradient of $V$ vanishes at $x = 0$ while $\dot x = 1$ there. The Lyapunov inequality needs only the weaker monotonicity assumption. With the LaSalle invariance principle, each bounded trajectory converges to the largest invariant set in $\{\dot V = 0\}$, and the paper uses this, together with an analysis of the equilibrium set (which may be infinite but totally disconnected), to prove approach to equilibria for broad classes of such networks under its stated regularity, positivity and boundedness hypotheses (Sections IV–V).

## Proof depends on

- [LaSalle's invariance principle](../../../Dynamics/smooth-dynamics/lasalle-s-invariance-principle/lasalle.md)

## Expansion

1. The model (1), with the regularity of $a_i$, $b_i$, $d_i$ needed for existence of solutions, and the additive and shunting networks of Section I as examples.
2. The derivative identity for $V$ (a direct computation using the symmetry of $C$) and the sign condition under $a_i \ge 0$ and nondecreasing $d_i$; the gradient form when each $d_i' > 0$.
3. The convergence theorem: [LaSalle's invariance principle](../../../Dynamics/smooth-dynamics/lasalle-s-invariance-principle/lasalle.md) puts the $\omega$-limit set in $\{\dot V = 0\}$, and a totally disconnected equilibrium set forces convergence to a single equilibrium.
4. The positivity and boundedness hypotheses of the source under which trajectories stay where these conditions hold.
5. The specialization to the continuous Hopfield network.

## Sources

- M. A. Cohen and S. Grossberg, Absolute stability of global pattern formation and parallel memory storage by competitive neural networks, IEEE Trans. Syst. Man Cybern. SMC-13 (1983), 815–826, Eq. (1) and Sections III–IV. <https://doi.org/10.1109/TSMC.1983.6313075>
