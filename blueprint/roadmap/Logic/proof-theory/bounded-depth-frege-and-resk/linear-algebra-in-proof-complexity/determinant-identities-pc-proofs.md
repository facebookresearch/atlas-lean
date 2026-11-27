# Short arithmetic proofs of the determinant identities

Over every field there is a circuit for the determinant such that $\det(XY)=\det(X)\det(Y)$ and $\det(Z)=z_{11}\cdots z_{nn}$ for triangular $Z$ have polynomial-size $\mathbb P_c$ proofs with circuits of depth $O(\log^2 n)$, and a formula for which these identities have $\mathbb P_f$ proofs of size $n^{O(\log n)}$.

The determinant is the unique function satisfying, for all $n\times n$ matrices $X,Y$ and every upper or lower triangular matrix $Z$ with diagonal $z_{11},\dots,z_{nn}$,

$$
\det(X\cdot Y)=\det(X)\cdot\det(Y),\qquad \det(Z)=z_{11}\cdots z_{nn}.
$$

Matrices have circuits as entries, and a matrix equation stands for the equations between corresponding entries.

**Theorem.** For any field $\mathbb F$:

1. There is a circuit $\det$ such that both identities have polynomial-size [$\mathbb P_c(\mathbb F)$](arithmetic-proof-systems.md) proofs, in which every circuit has depth $O(\log^2 n)$ (with $z_{11}\cdots z_{nn}$ written as a formula of depth $O(\log n)$).
2. There is a formula $\det$ such that both identities have $\mathbb P_f(\mathbb F)$ proofs of size $n^{O(\log n)}$.

Consequences proved in the same framework, with $\det$ the circuit (respectively formula) of the theorem, include: every formula $F$ of size $s$ satisfies $F=\det(M)$ for a $2s\times2s$ matrix $M$ of variables and field elements, with a polynomial-size $O(\log^2 s)$-depth $\mathbb P_c(\mathbb F)$ proof; and the equations $YX=I_n$ have polynomial-size $O(\log^2 n)$-depth $\mathbb P_c(\mathbb F)$ proofs from the assumptions $XY=I_n$; other properties such as the cofactor expansion and the Cayley-Hamilton theorem also have polynomial-size $\mathbb P_c$ proofs.

## Expansion

The proof follows the oblivious route to Berkowitz-type formulas, but inside the proof system. The determinant is first computed as a rational function by Gaussian elimination (an LU-style decomposition), whose properties are proved in a system $\mathbb P_I$ that allows division gates. Division gates are then eliminated, over large enough fields by Strassen's Taylor-series technique and over small fields by simulating a large extension field inside the small one; homogenization bounds degrees in $\mathbb P_c$ proofs. Finally [balancing of $\mathbb P_c$ proofs](balancing-pc-proofs.md) brings every circuit to depth $O(\log^2 n)$ and gives the quasipolynomial $\mathbb P_f$ proofs. Over $GF(2)$ the result yields [NC$^2$-Frege proofs of the determinant identities and of the inversion principle](nc2-frege-determinant-and-inversion.md).

## Depends on

- [Arithmetic proof systems for polynomial identities](arithmetic-proof-systems.md)

## Proof depends on

- [Balancing of Pc proofs and quasipolynomial simulation by Pf](balancing-pc-proofs.md)
- [Homogenization and division elimination for arithmetic circuits](../../../../TheoryOfComputation/algebraic-complexity/depth-reduction-and-chasms/homogenization-lemma.md)

## Sources

- Pavel Hrubeš and Iddo Tzameret, "Short Proofs for the Determinant Identities", *SIAM Journal on Computing*, 2015 (conference version STOC 2012), https://doi.org/10.1137/130917788; numbering as in arXiv:1112.6265v2 (Section 2.1, Theorem 4 (main theorem); Section 2.5, Propositions 11 and 12; Sections 3-7; Section 8, Proposition 39 (Theorem 4 rephrased); Section 9, Propositions 40-42 (cofactor expansion, inversion, Cayley-Hamilton)).
