# Kron reduction is invariant under relabeling of interior nodes

Let $m$, $p$, $q$ be finite index types and $e : q \to p$ a bijection. Let $A \in \mathbb{R}^{m \times m}$, $B \in \mathbb{R}^{m \times p}$, $D \in \mathbb{R}^{p \times p}$, $\varphi_P, j_P \in \mathbb{R}^m$ and $j_I \in \mathbb{R}^p$. Define the relabeled data $B'_{ik} = B_{i\,e(k)}$, $D'_{kl} = D_{e(k)\,e(l)}$ and $j_I' = j_I \circ e$, and write $K(A, B, D) = A - B\,D^{-1}B^{\mathsf T}$. Then

1. $K(A, B', D') = K(A, B, D)$;
2. $j_P - B'\,D'^{-1} j_I' = j_P - B\,D^{-1} j_I$;
3. $D'^{-1}(j_I' - B'^{\mathsf T}\varphi_P) = \big(D^{-1}(j_I - B^{\mathsf T}\varphi_P)\big) \circ e$;
4. $j_I' \cdot D'^{-1} j_I' = j_I \cdot D^{-1} j_I$.

No invertibility of $D$ is assumed: $D^{-1}$ is the matrix inverse extended by $D^{-1} = 0$ when $D$ is singular.
