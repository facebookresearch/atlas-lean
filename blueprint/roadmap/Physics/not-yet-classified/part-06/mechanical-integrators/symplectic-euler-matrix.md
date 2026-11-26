# Symplectic Euler step matrix

For real $m$ (mass), $k$ (stiffness) and $h$ (time step), the momentum-first (symplectic Euler) step matrix of the harmonic oscillator, acting on the state $(q, p)$, is

$$M = \begin{pmatrix} 1 - \dfrac{h^2 k}{m} & \dfrac{h}{m} \\[4pt] -h k & 1 \end{pmatrix},$$

the matrix of the update $p' = p - h k q$, $q' = q + h p'/m$. For $m = 0$ the entries take the convention $x/0 = 0$.
