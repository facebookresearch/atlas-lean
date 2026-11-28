# Curve integral of a constant field along a reversed segment

Along the straight segment from $(1, 2)$ to $(0, 0)$ in $\mathbb{R}^2$, traversed as the reverse of the segment from $(0, 0)$ to $(1, 2)$, the curve integral of the constant field $E = -(3, -1)$, that is of the linear form $x \mapsto \langle -(3, -1), x \rangle$, equals

$$\int_{(1,2) \to (0,0)} E \cdot dx = 1.$$

Reversing the path negates the integral along [the forward segment](curve-integral-affine-field-segment.md), which is $-1$. The field is $-\nabla \varphi$ for the affine potential $\varphi(x) = \langle (3, -1), x \rangle + d$, and the value is $\varphi(1, 2) - \varphi(0, 0) = 1$.
