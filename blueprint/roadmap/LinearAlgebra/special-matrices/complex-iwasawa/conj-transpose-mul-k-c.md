# Conj Transpose mul k C

Let $g = \begin{pmatrix} g_{11} & g_{12} \\ g_{21} & g_{22} \end{pmatrix}$ be a complex $2 \times 2$ matrix and $z \in \mathbb{C}$. Write $P(z) = g_{11} + z\, g_{21}$, $Q(z) = g_{12} + z\, g_{22}$ and $r(z) = \sqrt{\lvert P(z) \rvert^2 + \lvert Q(z) \rvert^2}$. Let

$$k(z) = \frac{1}{r(z)} \begin{pmatrix} \overline{Q(z)} & -\overline{P(z)} \\ P(z) & Q(z) \end{pmatrix}.$$

If $\det g \neq 0$, then

$$k(z)^{*} k(z) = I,$$

where $k(z)^{*}$ is the conjugate transpose.
