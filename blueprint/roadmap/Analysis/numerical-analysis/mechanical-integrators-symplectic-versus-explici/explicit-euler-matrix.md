# Explicit Euler step matrix for the harmonic oscillator

For mass $m$, stiffness $k$ and step $h$ (real), the explicit Euler step for the harmonic oscillator on the state $(q, p)$ is $q' = q + hp/m$, $p' = p - hkq$. Its matrix in $(q, p)$ coordinates is

$$M_{\mathrm{EE}} = \begin{pmatrix} 1 & h/m \\ -hk & 1 \end{pmatrix},$$

with $h/m = 0$ when $m = 0$.
