# Time derivative of the Cole–Hopf transform

Let $\nu \in \mathbb{R}$ and let $\varphi : \mathbb{R}^2 \to \mathbb{R}$ be $C^3$. Let $u(t,x) = -2\nu\, \partial_x \varphi(t,x) / \varphi(t,x)$ be the classical Cole–Hopf transform. At every $(t, x)$ with $\varphi(t,x) \ne 0$, $s \mapsto u(s, x)$ is differentiable at $t$ with

$$\partial_t u(t,x) = -2\nu\, \frac{\partial_x(\partial_t \varphi)(t,x)\, \varphi(t,x) - \partial_x \varphi(t,x)\, \partial_t \varphi(t,x)}{\varphi(t,x)^2},$$

where $\partial_x(\partial_t \varphi)(t, x)$ is the $x$-derivative at $x$ of $y \mapsto \partial_t \varphi(t, y)$, the order in which the theorem states it; by the equality of mixed partial derivatives of a $C^2$ function it equals $\partial_t(\partial_x \varphi)(t, x)$.
