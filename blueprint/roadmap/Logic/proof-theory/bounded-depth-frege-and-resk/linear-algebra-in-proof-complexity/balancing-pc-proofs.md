# Balancing of $\mathbb P_c$ proofs and quasipolynomial simulation by $\mathbb P_f$

A size-$s$ $\mathbb P_c$ proof of $F=G$ between circuits of syntactic degree at most $d$ can be rebuilt with every circuit of depth $O(\log s\log d+\log^2 d)$, and for formulas it yields a $\mathbb P_f$ proof of size $(s(d+1))^{O(\log d)}\le s^{O(\log s)}$, unlike any known Frege versus extended Frege simulation.

For a circuit $F$ of syntactic degree $d$, let $[F]$ denote the balanced circuit obtained by the Valiant-Skyum-Berkowitz-Rackoff construction, of size $\mathrm{poly}(s,d)$ and depth $O(\log^2d+\log s\log d)$, computing $\widehat F$.

**Theorem (balancing).** Let $F,G$ be circuits of syntactic degree at most $d$ such that $F=G$ has a [$\mathbb P_c$](arithmetic-proof-systems.md) proof of size $s$. Then:

1. $[F]=[G]$ has a $\mathbb P_c$ proof of size $\mathrm{poly}(s,d)$ and depth $O(\log s\cdot\log d+\log^2d)$;
2. if $F,G$ have depth at most $k$, then $F=G$ has a $\mathbb P_c$ proof of size $\mathrm{poly}(s,d)$ and depth $O(k+\log s\cdot\log d+\log^2d)$.

**Theorem (simulation).** If $F,G$ are formulas of syntactic degree at most $d$ and $F=G$ has a $\mathbb P_c$ proof of size $s$, then $F=G$ has a $\mathbb P_f$ proof of size $(s(d+1))^{O(\log d)}\le s^{O(\log s)}$.

**Proposition (homogenization).** If $F=G$ has a $\mathbb P_c$ proof of size $s$, then for every $k$ the degree-$k$ homogeneous parts $F^{(k)}=G^{(k)}$ have a $\mathbb P_c$ proof of size $s\cdot\mathrm{poly}(k)$ and syntactic degree at most $k$; and if $\deg F,\deg G\le d$, then $F=G$ has a $\mathbb P_c$ proof of syntactic degree at most $d$ and size $s\cdot\mathrm{poly}(d)$.

## Expansion

The proof mirrors [Valiant-Skyum-Berkowitz-Rackoff depth reduction](../../../../TheoryOfComputation/algebraic-complexity/depth-reduction-and-chasms/vsbr-depth-reduction.md) inside the proof system. Each circuit in the proof is replaced by its balanced version $[F]$, whose nodes compute partial derivative polynomials $\partial_wF_v$, and a main simulation lemma shows that every proof step between unbalanced circuits becomes a short derivation between balanced ones; homogenization first bounds the syntactic degree of all circuits in the proof by $d$. Unfolding a depth-$D$ circuit of size $S$ into a formula costs $S^{O(D)}$, which gives the quasipolynomial $\mathbb P_f$ simulation. In particular polynomial-size $\mathbb P_c$ proofs of identities of polynomial syntactic degree collapse to polynomial-size $O(\log^2n)$-depth proofs, which is what makes the [determinant proofs](determinant-identities-pc-proofs.md) shallow.

## Depends on

- [Arithmetic proof systems for polynomial identities](arithmetic-proof-systems.md)

## Proof depends on

- [Valiant–Skyum–Berkowitz–Rackoff depth reduction](../../../../TheoryOfComputation/algebraic-complexity/depth-reduction-and-chasms/vsbr-depth-reduction.md)

## Sources

- Pavel Hrubeš and Iddo Tzameret, "Short Proofs for the Determinant Identities", *SIAM Journal on Computing*, 2015 (conference version STOC 2012), https://doi.org/10.1137/130917788; numbering as in arXiv:1112.6265v2 (Section 2.2, Theorems 5 and 6 and Proposition 7; Section 3, Lemmas 15 and 16; Section 4, Theorem 17 (Valiant et al.), Lemma 19, Lemma 20 (main simulation lemma), Theorems 21 and 22 (restatements)).
