# Windowed scattering transform

For $J \in \mathbb{Z}$ and a path $p = (2^{j_1}, \dots, 2^{j_m})$ with every $2^{j_k} > 2^{-J}$ (the path set $P_J$),

$$S_J[p] f = U[p] f \star \varphi_{2^J} = |\,|f \star \psi_{2^{j_1}}| \star \cdots | \star \psi_{2^{j_m}}| \star \varphi_{2^J}$$

(S. Mallat, *Group invariant scattering*, Comm. Pure Appl. Math. 65 (2012), 1331–1398 (arXiv:1101.2286), Definition 2.4, equation (22)), in dimension $d = 1$ for real-valued signals, where the rotation group is $\{1, -1\}$ and paths use only the positive rotation. The empty path gives the low-pass average $A_J f$.
