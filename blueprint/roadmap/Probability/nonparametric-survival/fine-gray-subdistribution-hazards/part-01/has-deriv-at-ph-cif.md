# Derivative of the closed-form cumulative incidence

For $\theta, t \in \mathbb{R}$ let

$$
\phi(\theta, t) = 1 - \exp\left(-\theta \frac{t}{1+t}\right), \qquad \phi'(\theta, t) = \frac{\theta}{(1+t)^2} \exp\left(-\theta \frac{t}{1+t}\right),
$$

as in the [closed-form cumulative incidence](ph-cif.md) and [its derivative](ph-cif-deriv.md), with real division ($a/0 = 0$).

For every $\theta \in \mathbb{R}$ and every $t \in \mathbb{R}$ with $1 + t \ne 0$, the function $s \mapsto \phi(\theta, s)$ is differentiable at $t$ with derivative $\phi'(\theta, t)$:

$$
\frac{d}{dt}\left(1 - \exp\left(-\theta \frac{t}{1+t}\right)\right) = \frac{\theta}{(1+t)^2} \exp\left(-\theta \frac{t}{1+t}\right).
$$
