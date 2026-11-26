# Kron reduction to one port gives a Thevenin equivalent

Let $p$ be a finite set of interior nodes and let the conductance matrix

$$G = \begin{pmatrix} A & B \\ B^{\mathsf T} & D \end{pmatrix}$$

be positive definite, where $A \in \mathbb{R}^{1\times 1}$ is the port block, $B \in \mathbb{R}^{1\times p}$ and $D \in \mathbb{R}^{p\times p}$. Let $V, j_S, I \in \mathbb{R}$ and $\varphi_I, j_I \in \mathbb{R}^p$ satisfy

$$A V + B\varphi_I = j_S - I, \qquad B^{\mathsf T} V + D\varphi_I = j_I.$$

Set $K = A - B D^{-1} B^{\mathsf T}$ (the Schur complement, a scalar) and $j_{\mathrm{eff}} = j_S - B D^{-1} j_I$. Then $K > 0$,

$$K V = j_{\mathrm{eff}} - I, \qquad\text{and}\qquad V = \frac{j_{\mathrm{eff}}}{K} - \frac{1}{K}\, I.$$
