# The wide generalized Cohn tree

Fix a natural number $k$ and an integer $\ell$, and let
$S = \begin{pmatrix} k & 0 \\ 3k^2 + 3k & k \end{pmatrix}$. The wide $k$-generalized Cohn tree
$\mathrm{WGCT}(k, \ell)$ is the binary tree of triples of $2 \times 2$ integer matrices whose
root is $(P_{1;\ell}, Q_{1;\ell}, R_{1;\ell})$, where

$$P_{1;\ell}=\begin{pmatrix}\ell & 1\\ -\ell^2+2k\ell+3\ell-1 & -\ell+2k+3\end{pmatrix},$$



$$Q_{1;\ell}=\begin{pmatrix}k+\ell+1 & 1\\ k^2-\ell^2+3k+\ell+1 & k-\ell+2\end{pmatrix},$$



$$R_{1;\ell}=\begin{pmatrix}2k+\ell+2 & 1\\ -\ell^2-2k\ell+2k-\ell+1 & -\ell+1\end{pmatrix},$$

and in which a vertex $(P, Q, R)$ has left child $(P, PQ - S, Q)$ and right child
$(Q, QR - S, R)$. For a path $w$, a finite sequence of left and right steps, the vertex of
$\mathrm{WGCT}(k, \ell)$ at $w$ is the triple reached from the root by taking the steps of $w$ in
order; the empty path gives the root.

## Sources

- Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 3.1.
