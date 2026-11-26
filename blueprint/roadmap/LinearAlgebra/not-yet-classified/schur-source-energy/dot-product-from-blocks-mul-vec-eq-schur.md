# Schur energy identity with a source term (reconstruction form)

Let $m$ and $p$ be finite index sets, $A \in \mathbb{R}^{m \times m}$, $B \in \mathbb{R}^{m \times p}$ and $D \in \mathbb{R}^{p \times p}$ invertible and symmetric, and let

$$G = \begin{pmatrix} A & B \\ B^{\mathsf T} & D \end{pmatrix}, \qquad K = A - B D^{-1} B^{\mathsf T}.$$

For port potentials $\varphi_P \in \mathbb{R}^m$, a source $j_I \in \mathbb{R}^p$ and interior potentials $\varphi_I = D^{-1}(j_I - B^{\mathsf T}\varphi_P)$, the vector $\varphi = (\varphi_P, \varphi_I)$ satisfies

$$\varphi^{\mathsf T} G \varphi = \varphi_P^{\mathsf T} K \varphi_P + j_I^{\mathsf T} D^{-1} j_I.$$

No positivity is assumed.
