# Twist and internal torque of a fixed-traction shaft

Let $GJ > 0$, $L, T \in \mathbb{R}$ and $t, \varphi : \mathbb{R} \to \mathbb{R}$. Suppose $\varphi$ solves the fixed-traction problem with rigidity $GJ$, distributed torque $t$ and end torque $T$: $\varphi$ is $C^2$ on $[0, L]$, $-GJ\,\varphi''(x) = t(x)$ for every $x \in [0, L]$, $\varphi(0) = 0$ and $GJ\,\varphi'(L) = T$, all derivatives taken within $[0, L]$. Then for every $x \in [0, L]$,

$$\varphi(x) = \int_0^x \frac{T + \int_y^L t(z)\,dz}{GJ}\,dy \qquad\text{and}\qquad GJ\,\varphi'(x) = T + \int_x^L t(y)\,dy.$$
