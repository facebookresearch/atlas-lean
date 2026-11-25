# Kron reduction of a positive-definite conductance matrix

Let $m$ and $p$ be finite index types, and let $A \in \mathbb{R}^{m \times m}$, $B \in \mathbb{R}^{m \times p}$ and $D \in \mathbb{R}^{p \times p}$ be such that the block matrix

$$G = \begin{pmatrix} A & B \\ B^{\mathsf T} & D \end{pmatrix}$$

is positive definite. Write $K = A - B\,D^{-1}B^{\mathsf T}$. Let $\varphi_P, j_P \in \mathbb{R}^m$ and $\varphi_I, j_I \in \mathbb{R}^p$ satisfy $A\varphi_P + B\varphi_I = j_P$ and $B^{\mathsf T}\varphi_P + D\varphi_I = j_I$. Then

1. $K$ is positive definite;
2. $K\varphi_P = j_P - B\,D^{-1} j_I$;
3. $\varphi_I = D^{-1}(j_I - B^{\mathsf T}\varphi_P)$;
4. $(\varphi_P, \varphi_I) \cdot G(\varphi_P, \varphi_I) = \varphi_P \cdot K\varphi_P + j_I \cdot D^{-1} j_I$.
