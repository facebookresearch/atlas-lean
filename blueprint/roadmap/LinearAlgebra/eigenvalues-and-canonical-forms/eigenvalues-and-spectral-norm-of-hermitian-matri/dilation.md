# Hermitian dilation

For a rectangular matrix $B \in \mathbb{K}^{m \times n}$, the Hermitian dilation is the $(m+n) \times (m+n)$ block matrix

$$\mathscr{H}(B) = \begin{bmatrix} 0 & B \\ B^* & 0 \end{bmatrix},$$

indexed by the disjoint union of the row and column index sets. Tropp calls dilations "extraordinarily fruitful": through $\mathscr{H}$, concentration inequalities for Hermitian matrices transfer to rectangular ones, because $\lambda_{\max}(\mathscr{H}(B)) = \|B\|$ (display (2.1.28)).

## Sources

- J. A. Tropp, An Introduction to Matrix Concentration Inequalities, Found. Trends Mach. Learn. 8 (2015), 1–230, arXiv:1501.01571, Definition 2.1.5, display (2.1.26).
