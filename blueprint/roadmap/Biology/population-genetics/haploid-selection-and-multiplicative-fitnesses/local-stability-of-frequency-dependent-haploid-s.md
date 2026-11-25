# Local stability of frequency-dependent selection and a mean-fitness counterexample

Let $w_1,w_2:[0,1]\to(0,\infty)$ be $C^1$, and define the discrete
haploid [selection map](../natural-selection-fisher-s-theorem-and-the-price/select.md)

$$F(x)=\frac{xw_1(x)}{\bar w(x)},\qquad
 \bar w(x)=xw_1(x)+(1-x)w_2(x).$$

At an interior fixed point $x^*$ one has
$w_1(x^*)=w_2(x^*)=w^*>0$, and

$$F'(x^*)=1+\frac{x^*(1-x^*)[w'_1(x^*)-w'_2(x^*)]}{w^*}.$$

Thus $|F'(x^*)|<1$ implies local asymptotic stability and
$|F'(x^*)|>1$ implies instability. Equality at either $+1$ or $-1$ is
undecided by this test. Locally negative frequency dependence
$w'_1-w'_2<0$ gives $F'<1$ but need not give $F'>-1$:
for $w_1(x)=e^{-6(x-1/2)}$ and $w_2(x)=e^{6(x-1/2)}$, the fixed point
$1/2$ has derivative $-2$ and is unstable.

For a separately specified continuous-time model, use the replicator ODE

$$\dot x=G(x):=x(1-x)[w_1(x)-w_2(x)].$$

At the same interior equilibrium,
$G'(x^*)=x^*(1-x^*)[w'_1(x^*)-w'_2(x^*)]$.
A negative derivative implies local asymptotic stability, a positive one
instability, and zero is inconclusive. More generally, a strictly positive
$w_1-w_2$ immediately to the left of $x^*$ and a strictly negative one
immediately to the right imply local asymptotic stability. This is a scalar
ODE sign-change criterion, not a discrete-time criterion. The exponential
example has $G'(1/2)=-3$, so it is locally stable in this ODE despite being
unstable in the discrete map.

Mean fitness need not increase in the frequency-dependent discrete model.
Take $w_1(x)=1-x/2$, $w_2(x)=1-9x/10$, and $0<x_0<1$. Both fitnesses are
positive on $[0,1]$, and

$$F(x)-x=\frac{(2/5)x^2(1-x)}{\bar w(x)}>0\quad(0<x<1),\qquad
 \bar w(x)=1-9x/10+2x^2/5.$$

The trajectory increases to one, while $\bar w(x_t)$ decreases to $1/2$.
For an exact one-step witness, $x_0=1/2$ gives $x_1=15/26$ and mean fitness
$13/20$ followed by $415/676<13/20$. The initial value is not the functional
maximum $\bar w(0)=1$: $x_0=0$ would remain fixed.

## Depends on

- [Selection map](../natural-selection-fisher-s-theorem-and-the-price/select.md)

## Background

- [Mean-fitness increase for fixed fitnesses](../natural-selection-fisher-s-theorem-and-the-price/mean-fitness-le-mean-fitness-select.md)

## Expansion

Differentiate $F(x)-x=x(1-x)(w_1-w_2)/\bar w$ at its interior zero.
For $|F'|<1$, continuity of the derivative gives a local contraction; for
$|F'|>1$, a local expansion forces nearby nonfixed points to leave a small
neighborhood. For the ODE, local uniqueness and the inward sign pattern
keep nearby paths on their side of the equilibrium, monotone toward it;
a limit elsewhere would have nonzero derivative, a contradiction.

In the mean-fitness example, $\bar w'(x)=-9/10+4x/5<0$ and the only fixed
points are zero and one, so monotone convergence from $0<x_0<1$ gives the
claims. The fixed-fitness monotonicity theorem compares frequencies using
the same fitness vector before and after selection; it does not apply when
the vector itself changes with frequency.

## Sources

- J. Felsenstein, *Theoretical Evolutionary Genetics* (2019), <https://felsenst.github.io/pgbook/pgbook.pdf>, II.12, p. 117, for frequency-dependent fitnesses and possible oscillatory dynamics. The derivative tests, separately specified ODE criterion and exact examples above are derived here.
