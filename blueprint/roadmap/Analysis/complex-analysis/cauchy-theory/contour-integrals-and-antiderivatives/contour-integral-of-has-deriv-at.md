# Fundamental theorem of contour integration

Let $U \subseteq \mathbb{C}$ be open and let
$F, f : \mathbb{C} \to \mathbb{C}$ be such that $F$ is complex-differentiable at every $z \in U$
with $F'(z) = f(z)$. Let $\gamma : [0, 1] \to \mathbb{C}$ be a path from $a$ to $b$ whose image
lies in $U$ and which is continuously differentiable on $[0, 1]$, with derivative $\gamma'$
(one-sided at the endpoints). If $t \mapsto f(\gamma(t))\,\gamma'(t)$ is integrable on $[0, 1]$,
then $\int_\gamma f(z)\,dz = F(b) - F(a)$, where
$\int_\gamma f(z)\,dz = \int_0^1 f(\gamma(t))\,\gamma'(t)\,dt$.

## Sources

- L. V. Ahlfors, Complex Analysis, 3rd ed., Ch. 4, §1.1 to §1.3 (line integrals).
