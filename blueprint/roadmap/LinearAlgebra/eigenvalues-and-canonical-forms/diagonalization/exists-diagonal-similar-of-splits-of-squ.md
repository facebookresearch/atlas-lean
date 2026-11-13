# Diagonalizability from a split characteristic polynomial and a squarefree minimal polynomial

Let $K$ be a field and let $A$ be a square matrix over $K$ with rows and columns indexed by a
finite type $n$. If the characteristic polynomial of $A$ splits over $K$ and the minimal
polynomial of $A$ (that is, of the linear map $x \mapsto Ax$ on $K^n$) is squarefree, then there
are matrices $P$ and $D$ over $K$ indexed by $n$, with $D$ diagonal and $P$ invertible, such that
$A = P D P^{-1}$.

Proof: A squarefree minimal polynomial makes the linear map $x \mapsto Ax$ semisimple, so it has a
basis of eigenvectors by the eigenbasis theorem for semisimple endomorphisms; conjugating by the
change-of-basis matrix from the standard basis gives the diagonal form.

## Sources

- R. A. Horn and C. R. Johnson, Matrix Analysis, 2nd ed., Cambridge University Press (2013), Theorem 1.3.12.
