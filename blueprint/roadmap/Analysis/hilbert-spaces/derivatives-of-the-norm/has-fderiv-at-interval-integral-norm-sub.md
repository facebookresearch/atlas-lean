# Fréchet derivative of a radial primitive through its centre

Let $E$ be a real inner product space, let $z_0 \in E$, and let $f : \mathbb{R} \to \mathbb{R}$ be continuous on $[0, \infty)$ with $f(0) = 0$. Write $F(w) = \int_0^{\|w - z_0\|} f(t)\, dt$ for the radial primitive of $f$ centred at $z_0$. Then $F$ is Fréchet differentiable at every $z \in E$, with derivative

$$
DF(z)\, h = \frac{f(\|z - z_0\|)}{\|z - z_0\|} \langle z - z_0, h \rangle \qquad (h \in E),
$$

including at the centre $z = z_0$, where the derivative is $0$ (the quotient being read as $0$ there). The hypothesis $f(0) = 0$ is what makes the centre case true.
