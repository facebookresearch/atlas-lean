# Integer polynomials encoded as lists of monomials

A polynomial $P \in \mathbb{Z}[x_0, x_1, \dots]$ in finitely many variables is encoded as a finite list of monomials. Each monomial is a pair $(c, (e_0, e_1, \dots, e_k))$ of an integer coefficient $c$ and a finite list of exponents, standing for $c\, x_0^{e_0} x_1^{e_1} \cdots x_k^{e_k}$; exponents beyond the end of the list are $0$. The polynomial is the sum of its monomials, and the empty list encodes $0$.
