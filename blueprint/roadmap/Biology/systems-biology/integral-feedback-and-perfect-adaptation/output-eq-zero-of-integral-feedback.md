# Integral feedback gives robust perfect adaptation

Let $P$ be a set of parameters and $E$ a real normed vector space, let $F \colon P \times E \to E$ be a
family of vector fields with outputs $y \colon P \times E \to \mathbb{R}$, and let $z \colon E \to \mathbb{R}$
have derivative $z'(x)$, a continuous linear functional, at every $x \in E$, with
$z'(x)(F(p, x)) = y(p, x)$ for all $p$ and $x$ (so $\dot z = y$ along every trajectory, for every
parameter). Then $y(p, x) = 0$ whenever $F(p, x) = 0$: the output vanishes at every equilibrium of
every $F(p, \cdot)$.
