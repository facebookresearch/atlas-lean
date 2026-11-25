# Complex Descartes theorem for signed radii

Let $c_1, \dots, c_4 \in \mathbb{C}$ and nonzero real numbers $s_1, \dots, s_4$ satisfy
$|c_i - c_j|^2 = (s_i + s_j)^2$ for $i \ne j$, and let $k_i = 1/s_i$. Then

$$\Big(\sum_i k_i c_i\Big)^2 = 2 \sum_i (k_i c_i)^2 \qquad \text{and} \qquad \Big(\sum_i k_i\Big)^2 = 2 \sum_i k_i^2 .$$

The $s_i$ are signed radii: positive for a circle whose interior is disjoint from the others, negative for a circle
enclosing the others, so that tangent circles have centers at distance $|s_i + s_j|$.

Proof. Put $u_j = c_j - c_1$ and $p_{jl} = \langle u_j, u_l \rangle$; the hypotheses determine every $p_{jl}$ in
terms of the $s_i$. The Gram determinant of the three plane vectors $u_2, u_3, u_4$ vanishes, and in terms of the
radii it is $-4$ times the numerator of $(\sum k_i)^2 - 2 \sum k_i^2$: this is the real Descartes relation. The
number $F_0 = (\sum_j k_j u_j)^2 - 2 \sum_j (k_j u_j)^2$ has $|F_0|^2$ equal to a polynomial in the $p_{jl}$, by
the planar identity $(a \times b)(c \times d) = (a \cdot c)(b \cdot d) - (a \cdot d)(b \cdot c)$; substituting the
radii, it is a multiple of the same numerator, so $F_0 = 0$. In the same way
$G = (\sum_i k_i)(\sum_j k_j u_j) - 2\sum_j k_j^2 u_j$ vanishes, and expanding around $c_1$ gives
$(\sum k_i c_i)^2 - 2\sum (k_i c_i)^2 = F_0 + 2 c_1 G + c_1^2 \big((\sum k_i)^2 - 2 \sum k_i^2\big) = 0$.
This argument is a direct verification; Lagarias, Mallows and Wilks obtain the theorem from the matrix
generalisations of their Section 3 (curvature-center coordinates).

## Sources

- J. C. Lagarias, C. L. Mallows and A. R. Wilks, *Beyond the Descartes circle theorem*, Amer. Math. Monthly 109 (2002) 338–361, arXiv:math/0101066v1, Theorem 1.1 and Theorem 2.1.
