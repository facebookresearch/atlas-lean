# PD control with gravity compensation drives a robot to a setpoint

Consider a robot with configuration $\theta \in \mathbb{R}^n$ and dynamics $M(\theta)\ddot\theta + C(\theta, \dot\theta)\dot\theta + g(\theta) = \tau$, where $M$ is continuously differentiable and symmetric with $m I \preceq M(\theta) \preceq \bar m I$ for constants $0 < m \le \bar m$, $C$ is continuous and linear in $\dot\theta$, $g$ is continuous, and the passivity property holds: $\dot M(\theta) - 2C(\theta, \dot\theta)$ is skew-symmetric, where $\dot M = \frac{d}{dt}M(\theta(t))$. Fix a setpoint $\theta_d$, positive definite $K_p, K_d \in \mathbb{R}^{n \times n}$, and the control $\tau = K_p(\theta_d - \theta) - K_d\dot\theta + g(\theta)$. Assume the closed loop is locally Lipschitz in $(\theta, \dot\theta)$. Let $V(\theta, \dot\theta) = \tfrac12(\theta_d - \theta)^\top K_p(\theta_d - \theta) + \tfrac12\dot\theta^\top M(\theta)\dot\theta$.

1. **Energy identity.** Along closed-loop solutions, $\frac{d}{dt}V = -\dot\theta^\top K_d\dot\theta \le 0$.
2. **Global solutions.** Every solution exists for all $t \ge 0$ and stays in the compact set $\{V \le V(\theta(0), \dot\theta(0))\}$.
3. **Convergence.** $\theta(t) \to \theta_d$ and $\dot\theta(t) \to 0$ as $t \to \infty$.

**Proof.** With $\theta_e = \theta_d - \theta$, the closed loop is $M\ddot\theta + C\dot\theta = K_p\theta_e - K_d\dot\theta$. Then $\dot V = -\dot\theta^\top K_p\theta_e + \dot\theta^\top M\ddot\theta + \tfrac12\dot\theta^\top\dot M\dot\theta = -\dot\theta^\top K_d\dot\theta + \tfrac12\dot\theta^\top(\dot M - 2C)\dot\theta$, and the last term vanishes by skew-symmetry. The bounds on $M$ and $K_p \succ 0$ make the sublevel sets of $V$ compact, so by part 1 a solution stays in a compact set and, by the exit-from-compacts property of maximal solutions, exists for all $t \ge 0$. For part 3, the autonomous closed loop generates a continuous semiflow on that compact sublevel set and $V$ is nonincreasing along it; by LaSalle's invariance principle, solutions approach the largest invariant subset of $\{\dot V = 0\} = \{\dot\theta = 0\}$. On an invariant set with $\dot\theta \equiv 0$, also $\ddot\theta \equiv 0$, so $K_p\theta_e = 0$ and $\theta = \theta_d$.

## Proof depends on

- [Solutions of locally Lipschitz ODEs that leave every compact set](../../../Analysis/ordinary-differential-equations/maximal-solutions-and-global-existence/ode-maximal-solution-exit-compact.md): global existence from boundedness
- [LaSalle's invariance principle](../../../Dynamics/smooth-dynamics/lasalle-s-invariance-principle/lasalle.md): convergence to the largest invariant subset of $\{\dot\theta = 0\}$

## Sources

- K. M. Lynch and F. C. Park, *Modern Robotics: Mechanics, Planning, and Control*, Cambridge University Press, 2017 (preprint, <http://modernrobotics.org>), Proposition 8.1 ($\dot M - 2C$ is skew-symmetric, p. 279) and Section 11.4.1, PD setpoint control with gravity compensation (11.38)–(11.39), the error energy (11.40)–(11.41) and $\dot V = -\dot\theta^\top K_d\dot\theta \le 0$ (11.43), with the convergence argument by LaSalle's invariance principle (pp. 432–433). The explicit bounds on $M$ that give compact sublevel sets and global existence are stated on the page.
