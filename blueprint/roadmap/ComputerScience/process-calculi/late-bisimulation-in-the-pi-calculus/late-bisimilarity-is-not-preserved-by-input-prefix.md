# Strong late bisimilarity is not preserved by input prefix

In the [late transition semantics](late-transition-semantics-of-the-pi-calculus.md), let $x, y, u, v$ be pairwise distinct names and $z$ any name other than $y$. Then

$$\bar x v . 0 \mid y(u) . 0 \mathrel{\dot\sim} \bar x v . y(u) . 0 + y(u) . \bar x v . 0,$$

but

$$z(y) . (\bar x v . 0 \mid y(u) . 0) \mathrel{\not\dot\sim} z(y) . (\bar x v . y(u) . 0 + y(u) . \bar x v . 0),$$

since after the input the bound name $y$ may be instantiated to $x$, and then the left-hand agent $\bar x v . 0 \mid x(u) . 0$ has a $\tau$-transition that the right-hand agent $\bar x v . x(u) . 0 + x(u) . \bar x v . 0$ lacks. Hence [strong late bisimilarity](strong-late-bisimilarity.md) is not preserved by input prefix, nor by substitution of names. Pairwise distinctness suffices but is more than needed; what must be excluded includes $u = x$: the summand $y(x) . \bar x v . 0$ binds the $x$ of its output, and the first equation fails.

## Depends on

- [Strong late bisimilarity](strong-late-bisimilarity.md)
- [Late transition semantics of the π-calculus](late-transition-semantics-of-the-pi-calculus.md)

## Sources

- R. Milner, J. Parrow and D. Walker, "A calculus of mobile processes, II", *Information and Computation* 100(1):41–77, 1992, <https://www.pure.ed.ac.uk/ws/files/16426068/A_Calculus_of_Mobile_Processes_II.pdf>, Section 2.1: equation (6), where $\bar x$ abbreviates the prefix $\bar x v$ and $y$ the prefix $y(u)$, equation (7), and the two agents $z(y).(\bar x \mid y)$ and $z(y).(\bar x . y + y . \bar x)$ discussed after Definition 9.
