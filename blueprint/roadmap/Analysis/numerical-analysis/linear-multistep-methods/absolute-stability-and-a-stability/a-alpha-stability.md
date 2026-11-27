# A(α)-stability

Let $R_A$ be the region of [absolute stability](absolute-stability.md) of a linear multistep method. For $\alpha \in (0, \pi/2)$ the method is *A(α)-stable* if $R_A$ contains the infinite wedge

$$W_\alpha = \{\bar h \in \mathbb{C} : \operatorname{Re} \bar h < 0,\ |\operatorname{Im} \bar h| < (-\operatorname{Re} \bar h)\tan\alpha\},$$

the open wedge of half-angle $\alpha$ about the negative real axis, symmetric under conjugation (with the argument taken in $[0, 2\pi)$, the points with $\pi - \alpha < \arg \bar h < \pi + \alpha$).

It is *A(0)-stable* if it is A(α)-stable for some $\alpha \in (0, \pi/2)$, and *A₀-stable* if $R_A$ contains the negative real axis. An [A-stable](a-stability.md) method is A(α)-stable for every $\alpha$. If all eigenvalues of the matrix of a linear system $y' = Ay$ lie in $W_\beta$, an A(β)-stable method integrates it with no restriction on the step size.

## Depends on

- [Absolute stability of a linear multistep method](absolute-stability.md)
- [A-stability](a-stability.md)

## Sources

- E. Süli, *Numerical Solution of Ordinary Differential Equations*, lecture notes, Mathematical Institute, University of Oxford, version of 2 March 2022, Section 4.1, Definition 12 and the remark after it. <https://people.maths.ox.ac.uk/suli/nsodes.pdf>
