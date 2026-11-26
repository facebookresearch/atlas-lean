# Symplectic Euler does not preserve oscillator energy

Let $E(q, p) = \dfrac{p^2}{2m} + \dfrac{k q^2}{2}$ with $m = k = 1$, and let $M = \begin{pmatrix} 0 & 1 \\ -1 & 1 \end{pmatrix}$ be the symplectic Euler step matrix for $m = k = h = 1$. Then

$$E\bigl(M (0, 1)^{\top}\bigr) \ne E(0, 1).$$
