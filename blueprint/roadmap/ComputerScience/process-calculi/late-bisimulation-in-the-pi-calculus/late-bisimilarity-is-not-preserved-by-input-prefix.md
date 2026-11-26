# Strong late bisimilarity is not preserved by input prefix

In the [late transition semantics](late-transition-semantics-of-the-pi-calculus.md), write $\bar x$ for $\bar x v . 0$ and $y$ for $y(u) . 0$. If $x \ne y$ and $u \ne v$, then
$$\bar x \mid y \mathrel{\dot\sim} \bar x . y + y . \bar x,$$
but
$$z(y) . (\bar x \mid y) \mathrel{\not\dot\sim} z(y) . (\bar x . y + y . \bar x),$$
since after the input the bound name $y$ may be instantiated to $x$, and then the left-hand agent has a $\tau$-transition that the right-hand agent lacks. Hence [strong late bisimilarity](strong-late-bisimilarity.md) is not preserved by input prefix, nor by substitution of names.

## Depends on

- [Strong late bisimilarity](strong-late-bisimilarity.md)

## Proof depends on

- [Strong late bisimilarity](strong-late-bisimilarity.md)

## Sources

- R. Milner, J. Parrow and D. Walker, "A calculus of mobile processes, II", *Information and Computation* 100(1):41–77, 1992, <https://www.pure.ed.ac.uk/ws/files/16426068/A_Calculus_of_Mobile_Processes_II.pdf>, Section 2.1: equation (6) and the two agents $z(y).(\bar x \mid y)$ and $z(y).(\bar x . y + y . \bar x)$ discussed after Definition 9.
