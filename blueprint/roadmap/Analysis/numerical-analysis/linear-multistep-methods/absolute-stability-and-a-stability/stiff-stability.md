# Stiff stability

A linear multistep method with region of [absolute stability](absolute-stability.md) $R_A$ is *stiffly stable* if there are positive real numbers $a$ and $c$ such that $R_A \supseteq R_1 \cup R_2$, where

$$R_1 = \{\bar h \in \mathbb{C} : \Re \bar h < -a\}, \qquad R_2 = \{\bar h \in \mathbb{C} : -a \le \Re \bar h < 0,\ -c \le \Im \bar h \le c\}.$$

The definition, due to Gear, asks for stability where the eigenvalues of the fast transients of a stiff problem lie (far to the left) and near the origin, where the slow transients lie.

## Depends on

- [Absolute stability of a linear multistep method](absolute-stability.md)

## Sources

- E. Süli, *Numerical Solution of Ordinary Differential Equations*, lecture notes, Mathematical Institute, University of Oxford, version of 2 March 2022, Section 4.1, Definition 13 and the motivation before it. <https://people.maths.ox.ac.uk/suli/nsodes.pdf>
