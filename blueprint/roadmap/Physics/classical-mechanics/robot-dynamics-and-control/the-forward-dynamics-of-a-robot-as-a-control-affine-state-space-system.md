# The forward dynamics of a robot as a control-affine state-space system

Let the equations of motion of an $n$-joint robot be $\tau = M(\theta)\ddot\theta + h(\theta, \dot\theta)$, where $M : \mathbb{R}^n \to \mathbb{R}^{n \times n}$ is continuously differentiable with $M(\theta)$ symmetric positive definite for every $\theta$, and $h : \mathbb{R}^n \times \mathbb{R}^n \to \mathbb{R}^n$ (Coriolis, centripetal, gravity and friction terms) is continuously differentiable. With the state $x = (\theta, \omega) \in \mathbb{R}^{2n}$, $\omega = \dot\theta$:

1. **State-space form.** A twice-differentiable $\theta$ satisfies the equations of motion for a joint-torque signal $\tau$ if and only if $x = (\theta, \dot\theta)$ satisfies

    $$\dot x = f(x) + G(x)\tau, \qquad f(\theta, \omega) = \begin{bmatrix} \omega \\ -M(\theta)^{-1}h(\theta, \omega) \end{bmatrix}, \quad G(\theta, \omega) = \begin{bmatrix} 0 \\ M(\theta)^{-1} \end{bmatrix}.$$

2. **Regularity.** $f$ and $G$ are continuously differentiable, hence locally Lipschitz. For every initial state and every piecewise-continuous torque signal there is a unique maximal solution, and for every locally Lipschitz feedback $\tau = k(x)$ the closed loop $\dot x = f(x) + G(x)k(x)$ is a locally Lipschitz ordinary differential equation.
3. **Equilibria.** For a constant torque $\tau_0$, the equilibria are exactly the states $(\theta^\ast, 0)$ with $h(\theta^\ast, 0) = \tau_0$; with $h(\theta, 0) = g(\theta)$ the gravity torque, holding a configuration at rest needs exactly the gravity torque $g(\theta^\ast)$.

**Proof.** Part 1 is the forward-dynamics identity $\ddot\theta = M(\theta)^{-1}(\tau - h(\theta, \dot\theta))$, valid because $M(\theta)$ is invertible. For part 2, $\theta \mapsto M(\theta)^{-1}$ is continuously differentiable by the adjugate formula, since $\det M(\theta) > 0$, and products and sums of continuously differentiable maps are continuously differentiable; a continuously differentiable map is locally Lipschitz, and existence and uniqueness of maximal solutions follow from the theory of locally Lipschitz equations, applied on the successive intervals where the torque is continuous and glued at the breakpoints. For part 3, $\dot x = 0$ means $\omega = 0$ and $M(\theta^\ast)^{-1}(\tau_0 - h(\theta^\ast, 0)) = 0$.

## Proof depends on

- [Solutions of locally Lipschitz ODEs that leave every compact set](../../../Analysis/ordinary-differential-equations/maximal-solutions-and-global-existence/ode-maximal-solution-exit-compact.md): maximal solutions of locally Lipschitz right-hand sides

## Background

- [PD control with gravity compensation drives a robot to a setpoint](pd-control-with-gravity-compensation-drives-a-robot-to-a-setpoint.md): a feedback law for this state-space system

## Sources

- K. M. Lynch and F. C. Park, *Modern Robotics: Mechanics, Planning, and Control*, Cambridge University Press, 2017 (preprint, <http://modernrobotics.org>), Chapter 8: the equations of motion (8.1) with a symmetric positive-definite mass matrix and the lumped term $h(\theta, \dot\theta)$, and the forward dynamics (8.2), $\ddot\theta = M^{-1}(\theta)(\tau - h(\theta, \dot\theta))$ (p. 271). The state-space form, its regularity and the equilibrium condition are derived on the page.
