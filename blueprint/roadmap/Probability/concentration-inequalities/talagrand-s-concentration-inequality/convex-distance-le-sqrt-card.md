# The convex distance is at most the square root of the Hamming distance

For every $y \in A$, $f_c(A, x) \le \sqrt{\operatorname{card}\{i : x_i \ne y_i\}}$: the indicator
vector of $\{i : x_i \ne y_i\}$ lies in $U_A(x)$ and has that Euclidean norm (Talagrand,
*Concentration of measure and isoperimetric inequalities in product spaces*, Publ. Math. IHÉS 81
(1995), Section 4.1). Together with Lemma 4.1.2 of the source, read with all weights
$\alpha_i = 1$, it places $f_c$ between the Hamming distance divided by $\sqrt N$ and the square
root of the Hamming distance.
