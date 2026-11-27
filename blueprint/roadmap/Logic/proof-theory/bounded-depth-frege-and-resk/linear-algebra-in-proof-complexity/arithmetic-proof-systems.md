# Arithmetic proof systems for polynomial identities

The systems $\mathbb P_f(\mathbb F)$ and $\mathbb P_c(\mathbb F)$ prove equations $F=G$ between arithmetic formulas, respectively circuits, over a field $\mathbb F$ using the equality rules and the commutative ring axioms; an equation is provable exactly when both sides compute the same polynomial.

An arithmetic circuit over a field $\mathbb F$ is a directed acyclic graph whose in-degree-0 nodes are labelled by variables or field elements and whose other nodes have in-degree two, labelled $+$ or $\times$, with one output node; it is a *formula* if every node has out-degree one. Size is the number of nodes and depth the length of a longest path; $\widehat F$ is the polynomial computed by $F$.

**$\mathbb P_f(\mathbb F)$.** Lines are equations $F=G$ between formulas. The rules are

$$
\frac{F=G}{G=F}\qquad\frac{F=G\quad G=H}{F=H}\qquad\frac{F_1=G_1\quad F_2=G_2}{F_1+F_2=G_1+G_2}\qquad\frac{F_1=G_1\quad F_2=G_2}{F_1\cdot F_2=G_1\cdot G_2}
$$

and the axioms are A1 $F=F$; A2 $F+G=G+F$; A3 $F+(G+H)=(F+G)+H$; A4 $F\cdot G=G\cdot F$; A5 $F\cdot(G\cdot H)=(F\cdot G)\cdot H$; A6 $F\cdot(G+H)=F\cdot G+F\cdot H$; A7 $F+0=F$; A8 $F\cdot0=0$; A9 $F\cdot1=F$; A10 $a=b+c$ and $a'=b'\cdot c'$ for field elements with these equations true in $\mathbb F$. A proof is a sequence of equations each an axiom or obtained by a rule; its size is the sum of the sizes of all formulas in it, and its number of lines is the number of equations.

**$\mathbb P_c(\mathbb F)$.** The same rules and axioms with $F,G,H$ ranging over circuits, together with C1 $F_1\oplus F_2=F_1+F_2$ and C2 $F_1\otimes F_2=F_1\cdot F_2$, where $F_1\oplus F_2$ is a circuit whose output gate adds the outputs of (possibly shared) subcircuits $F_1,F_2$, and $F_1+F_2$ uses disjoint copies. The depth of a $\mathbb P_c$ proof is the maximal depth of a circuit in it.

**Proposition.** For formulas $F,G$, $\mathbb P_f(\mathbb F)$ proves $F=G$ if and only if $\widehat F=\widehat G$; for circuits $F,G$, $\mathbb P_c(\mathbb F)$ proves $F=G$ if and only if $\widehat F=\widehat G$. Moreover $\mathbb P_c$ and extended $\mathbb P_f$ (with extension axioms $z_i=F_i$) polynomially simulate each other, and a $\mathbb P_c$ proof with $k$ lines between circuits of size $s$ yields a $\mathbb P_c$ proof of size $\mathrm{poly}(s,k)$.

## Expansion

Soundness is by induction on the proof and completeness by rewriting both sides as sums of monomials. Proofs are closed under substitution of formulas, respectively circuits, for variables. $\mathbb P_f$ and $\mathbb P_c$ are algebraic analogues of Frege and of circuit Frege (equivalently extended Frege), and over $GF(2)$ they are restricted versions of their propositional counterparts. A short proof of every true identity would put polynomial identity testing in NP. Unlike Frege and extended Frege, these systems [admit balancing and a quasipolynomial simulation of $\mathbb P_c$ by $\mathbb P_f$](balancing-pc-proofs.md).

## Depends on

- [Arithmetic circuit](../../../../TheoryOfComputation/algebraic-complexity/arithmetic-circuits/arithmetic-circuit.md)

## Proof depends on

None.

## Sources

- Pavel Hrubeš and Iddo Tzameret, "Short Proofs for the Determinant Identities", *SIAM Journal on Computing*, 2015 (conference version STOC 2012), https://doi.org/10.1137/130917788; numbering as in arXiv:1112.6265v2 (Section 1.1, definitions of the systems, Proposition 1, Proposition 2 and Remark 3).
