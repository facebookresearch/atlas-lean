# Capability and limits of feedback

For a discrete-time system with unknown structure, a feedback law is any sequence of causal maps
$u_t = h_t(y_0, \dots, y_t)$ of the observed outputs, without restriction to a parametrised family. Guo's programme
(Proc. ICM 2002, Vol. III, arXiv:math/0305011; Int. J. Adapt. Control Signal Process. 16 (2002) 341–354) asks how much
uncertainty the whole feedback mechanism can handle. For $y_{t+1} = \theta f(y_t) + u_t + w_{t+1}$ with Gaussian noise,
a Gaussian random parameter $\theta$ and a known $f$ growing like $M x^b$, the critical exponent is $b = 4$
(ICM 2002, Theorem 3.1). For the nonparametric system $y_{t+1} = f(y_t) + u_t + w_{t+1}$ with bounded noise and $f$ in
the ball of radius $L$ of the generalized Lipschitz quasi-norm, Xie and Guo (IEEE Trans. Automat. Control 45 (2000))
showed that the critical radius is $L = 3/2 + \sqrt 2$; the two halves are stated below.

The number $3/2 + \sqrt 2$ is the larger root of $L^2 - 3L + 1/4 = 0$, the discriminant of the characteristic
polynomial $z^2 - (L + 1/2) z + L$ of the recursion $a_{n+1} = (L + 1/2) a_n - L a_{n-1}$; Guo
(Int. J. Adapt. Control Signal Process. 16 (2002), remark after Theorem 3) relates stabilisability to the behaviour of
the solutions of this recursion.

- [Feedback can stabilise every system with uncertainty below $3/2 + \sqrt 2$](exists-feedback-bdd-above-of-lt.md)
- [No feedback stabilises every system with uncertainty at least $3/2 + \sqrt 2$](exists-unbounded-of-le.md)

## Related topics

- [Recursive least squares](../recursive-least-squares/README.md): the estimator inside the least-squares-based adaptive controllers whose performance these limits bound.
- [Nonlinear controllability and stabilisation](../nonlinear-controllability-and-stabilisation/README.md): Brockett's condition, another obstruction to stabilisation, for continuous stationary feedback of known systems.
- [Pole placement](../pole-placement/README.md): stabilisation of a known linear system by linear feedback, where no uncertainty has to be learned.
