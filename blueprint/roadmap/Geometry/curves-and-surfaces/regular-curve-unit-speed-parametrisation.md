# Unit-speed parametrisation of a regular space curve

Let $I$ be a nonempty open interval in $\mathbb R$, let $t_0\in I$, and let $\gamma:I\to\mathbb R^3$ be $C^1$ with $\gamma'(t)\ne0$ at every $t\in I$. Use the Euclidean norm. The signed arc-length coordinate

$$
s(t)=\int_{t_0}^{t}\|\gamma'(r)\|\,dr
$$

is a strictly increasing $C^1$ diffeomorphism from $I$ onto the open interval $J=s(I)$. It sends $t_0$ to zero and is negative to the left of $t_0$; it need not take every real value. The curve $\beta=\gamma\circ s^{-1}:J\to\mathbb R^3$ is $C^1$ and has speed one everywhere. It is the parameter change $s$, not the curve $\gamma$, that must be one-to-one.

For $a\le b$ in $I$, the restriction of $\gamma$ to $[a,b]$ has bounded variation: its length (the supremum of sums of successive chord lengths over partitions) is $L=s(b)-s(a)$. The map $q(t)=s(t)-s(a)$ takes $[a,b]$ onto $[0,L]$, and the traversal factors as

$$
\gamma|_{[a,b]}=\alpha\circ q,\qquad \alpha(u)=\beta(s(a)+u)\quad(0\le u\le L),
$$

where $\alpha$ is $1$-Lipschitz. This counts the traversal, including any repeated visits to the same point. For parameters in either order the unsigned subarc length is $|s(b)-s(a)|$.

## Proof

Write $v=\|\gamma'\|$. It is continuous and positive on $I$, so it is integrable between any two parameters; no integral over all of $I$ is needed. To use functions defined on the real line, extend $\gamma$ by zero off $I$: its values and derivatives near each point of $I$ are unchanged. Likewise the speed can be extended by zero. This integrand is continuous on a neighbourhood of each $t\in I$, hence almost everywhere strongly measurable there. The upper-endpoint fundamental theorem of calculus gives $s'(t)=v(t)$, also when $t<t_0$. Thus $s$ is $C^1$, and on each nondegenerate compact subinterval its secant slope is positive by the mean value theorem.

At every $t$, the one-dimensional inverse function theorem gives a $C^1$ local inverse on an open neighbourhood of $s(t)$ contained in $J$. Thus $J$ is open; the intermediate value theorem on intervals between parameters shows that it is an interval. Strict increase makes every local inverse a restriction of the same inverse $h:J\to I$. In particular $h$ is $C^1$ and $h'(s(t))=1/v(t)$. Apply the real scalar chain rule to each of the three coordinates of $\gamma\circ h$ at $s(t)$ (only values near $s(t)$ and $t$ matter). Together the three derivatives give $\beta'(s(t))=\gamma'(t)/v(t)$, of norm one.

The extension of $\gamma$ is $C^1$ on $[a,b]\subset I$, so the compact $C^1$ length formula identifies its variation there with $\int_a^b v$. To see why this is $s(b)-s(a)$ in any position relative to $t_0$, compare $t\mapsto\int_a^t v$ with $t\mapsto s(t)-s(a)$. Both vanish at $a$ and both have derivative $v$; their difference is constant by the mean value theorem. Continuity and monotonicity now give the stated range of $q$; substituting $s(a)+q(t)=s(t)$ gives the factorisation. For $x\le y$ in $J$, the chord from $\beta(x)$ to $\beta(y)$ is at most the variation of $\gamma$ between $h(x)$ and $h(y)$, namely $y-x$. Hence $\beta$ is $1$-Lipschitz, as is its translated restriction $\alpha$. If $a=b$, then $L=0$ and $\alpha$ sends the singleton $\{0\}$ to $\gamma(a)$.

## Depends on

- [Euclidean three-space](f-ry-milnor-theorem/space.md)
- [Velocity of a space curve](f-ry-milnor-theorem/velocity.md)
- [Oriented interval integral](../../MeasureTheory/integration/oriented-interval-integral.md)
- [Bounded variation on a set](../../MeasureTheory/real-functions/bounded-variation-and-total-variation/bounded-variation-on.md)

## Proof depends on

- [Derivative of an interval integral at the upper endpoint](../../Analysis/real-functions/integration/derivative-of-an-interval-integral-at-the-upper-endpoint.md)
- [Mean value theorem](../../Analysis/real-functions/differential-calculus/mean-value-theorem.md)
- [Inverse function theorem](../../Analysis/calculus-in-normed-spaces/inverse-function-theorem.md)
- [Intermediate value theorem](../../Analysis/real-functions/continuity-and-functional-equations/intermediate-value-theorem.md)
- [Scalar chain rule at a point](../../Analysis/calculus-in-normed-spaces/frechet-derivatives/chain-rule-holomorphic.md)
- [Length of a compact $C^1$ curve](../../Analysis/real-functions/multivariable-calculus/length-of-a-curve/curve-length-eq-integral-norm-deriv.md)

## Sources

- A. Petrunin and S. Zamora Barrera, [*What is differential geometry: curves and surfaces*](https://arxiv.org/pdf/2012.11814v7), Proposition 2.11, pp. 19–20, treats the smooth regular case.
- For the $C^1$ argument: Jiří Lebl, *Basic Analysis*, [§5.3, Theorem 5.3.3](https://www.jirka.org/ra/html/sec_ftc.html) (differentiating the primitive) and [§4.4, Lemma 4.4.1 and Theorem 4.4.2](https://www.jirka.org/ra/html/sec_ift.html) (inverting a real function with nonzero derivative).
- The length-interval factorisation is the regular-curve case of the question in the [Tau Ceti geometric measure theory roadmap, G1](https://github.com/TauCetiProject/TauCetiRoadmap/blob/8cc2f79f60ebc394160c214a3d0abd16c3c0aff9/TauCetiRoadmap/GeometricMeasureTheory/README.md#L106-L139).
