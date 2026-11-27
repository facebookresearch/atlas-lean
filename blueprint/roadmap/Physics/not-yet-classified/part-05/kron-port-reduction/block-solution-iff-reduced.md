# Block system is equivalent to the reduced port equation with reconstruction

Let $m$ and $p$ be finite index types, let $A \in \mathbb{R}^{m \times m}$, $B \in \mathbb{R}^{m \times p}$, and let $D \in \mathbb{R}^{p \times p}$ be invertible. Write $K = A - B\,D^{-1}B^{\mathsf T}$. For all $\varphi_P, j_P \in \mathbb{R}^m$ and $\varphi_I, j_I \in \mathbb{R}^p$,

$$\begin{cases} A\varphi_P + B\varphi_I = j_P \\ B^{\mathsf T}\varphi_P + D\varphi_I = j_I \end{cases} \iff \begin{cases} K\varphi_P = j_P - B\,D^{-1} j_I \\ \varphi_I = D^{-1}(j_I - B^{\mathsf T}\varphi_P). \end{cases}$$
