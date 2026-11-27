# Hermitian dilation

For a matrix $B$ with rows indexed by a set $m$, columns indexed by a set $n$ and entries in a set with a zero and a conjugation $x \mapsto x^*$ (such as $\mathbb{R}$ or $\mathbb{C}$), the Hermitian dilation is the block matrix

$$\mathscr{H}(B) = \begin{bmatrix} 0 & B \\ B^* & 0 \end{bmatrix},$$

indexed by the disjoint union $m \sqcup n$ of the row and column index sets, where $B^*$ is the conjugate transpose of $B$. Tropp calls dilations "extraordinarily fruitful": through $\mathscr{H}$, concentration inequalities for Hermitian matrices transfer to rectangular ones, because, for a finite real or complex matrix $B$ with at least one row or column, $\lambda_{\max}(\mathscr{H}(B)) = \|B\|$, the spectral norm of $B$ (display (2.1.28)).

## Sources

- J. A. Tropp, An Introduction to Matrix Concentration Inequalities, Found. Trends Mach. Learn. 8 (2015), 1–230, arXiv:1501.01571, Definition 2.1.5, display (2.1.26).
