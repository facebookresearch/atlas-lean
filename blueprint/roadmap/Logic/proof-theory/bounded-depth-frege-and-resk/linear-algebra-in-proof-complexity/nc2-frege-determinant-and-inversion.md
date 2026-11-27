# NC$^2$-Frege proofs of the determinant identities and the inversion principle

Over $GF(2)$, the determinant identities and the inversion principle $XY=I_n\rightarrow YX=I_n$ have polynomial-size circuit Frege proofs in which every circuit has depth $O(\log^2 n)$, that is NC$^2$-Frege proofs, and quasipolynomial-size Frege proofs.

**Theorem.** Interpret the identities $\det(XY)=\det(X)\det(Y)$ and $\det(Z)=z_{11}\cdots z_{nn}$ (for triangular $Z$), with the determinant circuit of the [main theorem](determinant-identities-pc-proofs.md), as Boolean tautologies over $GF(2)$. Then:

1. these properties of the determinant have polynomial-size circuit Frege proofs in which every circuit has depth at most $O(\log^2n)$, and quasipolynomial-size Frege proofs;
2. the implication $(XY=I_n)\rightarrow(YX=I_n)$ for $n\times n$ matrices $X,Y$ has a polynomial-size circuit Frege proof in which every circuit has depth at most $O(\log^2n)$, and a quasipolynomial-size Frege proof.

## Expansion

Over the two-element field, reading $+$ and $\cdot$ modulo $2$ as Boolean connectives and $=$ as logical equivalence, an $O(\log^2n)$-depth [$\mathbb P_c(GF(2))$](arithmetic-proof-systems.md) proof is formally an NC$^2$-Frege proof, and the quasipolynomial $\mathbb P_f$ proofs become Frege proofs. The inversion principle is one of the hard matrix identities proposed by Cook and Rackoff and studied by Soltys and Cook, who gave polynomial-size extended Frege proofs; it was conjectured to separate Frege from extended Frege, and the existence of polynomial-size NC$^2$-Frege proofs, conjectured by Bonet, Buss and Pitassi, had been open. The authors expect the result to extend to other finite fields and to the rationals after encoding field elements in binary. Superpolynomial Frege lower bounds remain [open](../../superpolynomial-lower-bounds-for-frege-proofs.md), and the weak rank principle builds on these identities: it follows from the inversion principle and so has [polynomial-size NC$^2$-Frege proofs](weak-rank-principle.md).

## Depends on

- [Arithmetic proof systems for polynomial identities](arithmetic-proof-systems.md)
- [Short arithmetic proofs of the determinant identities](determinant-identities-pc-proofs.md)

## Proof depends on

None.

## Sources

- Pavel Hrubeš and Iddo Tzameret, "Short Proofs for the Determinant Identities", *SIAM Journal on Computing*, 2015 (conference version STOC 2012), https://doi.org/10.1137/130917788; numbering as in arXiv:1112.6265v2 (Section 1, introduction; Section 2.5, Proposition 12, Theorem 13 and Remark 14).
