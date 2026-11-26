# Separable fields satisfy the source-free vacuum Maxwell equations

Let $c$ be a speed of light. Let $a : \mathbb{R} \to \mathbb{R}$ and $f : \mathbb{R}^2 \to \mathbb{R}$, $(t, z) \mapsto f(t, z)$, be $C^\infty$, let $k_c \in \mathbb{R}$, and assume the profile equation $a''(x) = -k_c^2\, a(x)$ for all $x$ and the mode equation

$$f_{tt}(t, z) = c^2 \big( f_{zz}(t, z) - k_c^2 f(t, z) \big) \quad \text{for all } t, z.$$

Define the fields on $(t, x, y, z)$

$$\mathbf E = \big(0,\ -a(x) f_t(t, z),\ 0\big), \qquad \mathbf B = \big(-a(x) f_z(t, z),\ 0,\ a'(x) f(t, z)\big).$$

Then $\mathbf E$ and $\mathbf B$ satisfy, at every $(t, x, y, z)$, the source-free vacuum Maxwell equations at speed of light $c$:

$$\operatorname{div} \mathbf E = 0,\quad \operatorname{div} \mathbf B = 0,\quad \operatorname{curl} \mathbf E = -\partial_t \mathbf B,\quad \operatorname{curl} \mathbf B = \frac{1}{c^2}\, \partial_t \mathbf E.$$

Here divergence, curl and time derivative are formed from one-variable derivatives in each coordinate.
