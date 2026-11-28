# Inverse of the symmetric Butler–Volmer relation

With equal transfer coefficients the Butler–Volmer current is $j=2j_0\sinh(\alpha nf\eta)$, a strictly increasing bijection of $\mathbb R$ inverted by $\eta=\frac{1}{\alpha nf}\operatorname{arsinh}\frac{j}{2j_0}$: each current density has exactly one activation overpotential, of the same sign.

In the [Butler–Volmer equation](butler-volmer-equation.md) take $\alpha_a=\alpha_c=\alpha>0$, with $j_0>0$, $n\ge1$, $T>0$ and
$f=F/(RT)$. Then

$$j(\eta)=2j_0\sinh(\alpha nf\eta),$$

and $j:\mathbb R\to\mathbb R$ is a strictly increasing bijection with inverse

$$\eta(\bar j)=\frac{1}{\alpha nf}\operatorname{arsinh}\!\Big(\frac{\bar j}{2j_0}\Big)=\frac{1}{\alpha nf}\ln\!\Big(\frac{\bar j}{2j_0}+\sqrt{1+\frac{\bar j^2}{4j_0^2}}\Big).$$

So each current density $\bar j$ has exactly one activation overpotential, and it has the sign of $\bar j$.

## Context

Undergraduate electrochemistry. Inverting Butler–Volmer is how battery and fuel-cell models turn an imposed current into an activation voltage loss; the symmetric case $\alpha=1/2$ is the common default.

## Depends on

- [Butler–Volmer equation](butler-volmer-equation.md)

## Proof depends on

None.

## Expansion

With $\alpha_a=\alpha_c$, $e^u-e^{-u}=2\sinh u$. The proof needs that $\sinh$ is a strictly increasing bijection of $\mathbb R$ with two-sided inverse $\operatorname{arsinh}y=\ln(y+\sqrt{1+y^2})$ (in Mathlib `Real.sinh_strictMono`, `Real.sinh_bijective`, `Real.sinh_arsinh`, `Real.arsinh_sinh`); a good expansion adds a page for these facts. Composing with the positive scalings $\eta\mapsto\alpha nf\eta$ and $y\mapsto2j_0y$ then gives the inverse and the sign (Lecture 13, Sec. 3C).

## Sources

- M. Z. Bazant, *10.626 Electrochemical Energy Systems*, MIT OpenCourseWare, Spring 2014, lecture notes, Lecture 13: Butler-Volmer equation, Sec. 3C (symmetric electron transfer: hyperbolic-sine form inverted by the inverse hyperbolic sine) and Fig. 2. [Lecture PDF](https://old.ocw.mit.edu/courses/chemical-engineering/10-626-electrochemical-energy-systems-spring-2014/lecture-notes/MIT10_626S14_S11lec13.pdf); [course](https://ocw.mit.edu/courses/10-626-electrochemical-energy-systems-spring-2014/)
