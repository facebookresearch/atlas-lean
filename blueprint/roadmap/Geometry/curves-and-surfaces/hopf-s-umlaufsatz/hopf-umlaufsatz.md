# Hopf's Umlaufsatz

Let $r : \mathbb{R} \to \mathbb{R}^2$ be a positively oriented simple
closed unit-speed plane curve: $r$ is continuously differentiable and $2\pi$-periodic, injective
on $[0, 2\pi)$, satisfies $\lVert r'(t) \rVert = 1$ for all $t$, and has positive signed area
$\frac{1}{2}\int_0^{2\pi} \det(r(t), r'(t))\,dt > 0$, where $\det(u, v) = u_0 v_1 - u_1 v_0$.
Let $\alpha : \mathbb{R} \to \mathbb{R}$ be a continuously differentiable tangent-angle lift of
$r$, that is, $r'(t) = (\cos \alpha(t), \sin \alpha(t))$ for all $t$. Then the total signed
curvature over one period is $2\pi$: $\int_0^{2\pi} \alpha'(t)\,dt = 2\pi$.

## Sources

- H. Hopf, *Über die Drehung der Tangenten...*, Compositio Math. 2 (1935). Knill, §170. Via leanprover/lean-eval@38361be, problem `hopf_umlaufsatz`.
