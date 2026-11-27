# Gradient-flow identity for the neural tangent kernel

Let $F : \mathbb R^P \to \mathbb R^n$ be $C^1$, $y \in \mathbb R^n$, and $L(\theta) = \tfrac12 \|F(\theta) - y\|^2$. If a parameter path satisfies $\theta'(t) = -\nabla L(\theta(t))$ at time $t$, then

$$\frac{d}{dt} F(\theta(t)) = -K(\theta(t))\,\big(F(\theta(t)) - y\big),$$

where $K(\theta) = J(\theta) J(\theta)^{\mathsf T}$ is the empirical neural tangent kernel and $J$ is the Jacobian of $F$.
