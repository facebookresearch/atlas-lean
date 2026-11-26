# Hodge–Tate weights of a locally algebraic character

This node is still to be broken down. Let $L$ and $K$ be finite extensions of $\mathbb{Q}_p$, let $C_L$ be the completion of an algebraic closure
of $L$, and let $\psi \colon G_L^{\mathrm{ab}} \to K^\times$ be a continuous character such that $V = K$, with
$G_L$ acting through $\psi$, is a [Hodge–Tate](../hodge-tate-representations.md) $\mathbb{Q}_p$-linear
representation. Use the arithmetic normalization of the
[local Artin map](../../../../p-adic-numbers/local-class-field-theory.md) $r_L$, which sends uniformizers to
arithmetic Frobenius elements. By [Tate's theorem](hodge-tate-characters-are-locally-algebraic.md) $\psi$ is
[locally algebraic](locally-algebraic-characters.md): with $K \otimes_{\mathbb{Q}_p} L = \prod_i F_i$ and quotient
maps $q_i$, there are integers $n_i$ with
$\psi(r_L(x)) = \prod_i N_{F_i/K}(q_i(1 \otimes x))^{-n_i}$ for $x$ near $1$ in $L^\times$.

The semilinear representation $C_L \otimes_{\mathbb{Q}_p} V$ of $G_L$ decomposes into $G_L$-stable $C_L$-lines
$V_\sigma$ indexed by the $\mathbb{Q}_p$-embeddings $\sigma \colon K \to C_L$ (the line on which $K$ acts through
$\sigma$), and $V_\sigma \cong C_L(w_\sigma)$ for an integer $w_\sigma$, the Hodge–Tate weight of $\psi$ at
$\sigma$, in the convention in which the cyclotomic character has weight $1$. Then for each $\sigma$

$$w_\sigma = n_i$$

for the unique $i$ such that the $L$-algebra map $\sigma \otimes 1 \colon K \otimes_{\mathbb{Q}_p} L \to C_L$
extending $\sigma$ factors through $q_i$. For $L = \mathbb{Q}_p$: if $\psi(r_{\mathbb{Q}_p}(x)) = x^{-n}$ near $1$,
then every $w_\sigma$ is $n$; for the cyclotomic character, $K = \mathbb{Q}_p$, whose weight is $1$, this gives $n = 1$.

A good expansion has pages for the two steps of Conrad's proof that no page states: that restricting a
Hodge–Tate representation of $G_L$ to $G_{F'}$ for a finite extension $F'/L$ keeps it Hodge–Tate with the same
Hodge–Tate numbers (Brinon–Conrad, Theorem 2.4.6, p. 20: $F' \otimes_L D_L(W) \cong D_{F'}(W)$ as graded
$F'$-vector spaces); and the Galois-theoretic description of the embeddings $\sigma$ whose $L$-algebra map
$\sigma \otimes 1$ factors through a given factor $F_i$ of $K \otimes_{\mathbb{Q}_p} L$ (end of Conrad's proof, p. 34).

## Depends on

- [Hodge–Tate characters of local Galois groups are locally algebraic](hodge-tate-characters-are-locally-algebraic.md), for the integers $n_i$
- [Locally algebraic characters of local Galois groups](locally-algebraic-characters.md)
- [Hodge–Tate representations](../hodge-tate-representations.md), for the weights
- [Local class field theory: the local Artin map](../../../../p-adic-numbers/local-class-field-theory.md), for the arithmetic normalization of $r_L$
- [Cyclotomic character and Tate twists](../../cyclotomic-character-and-tate-twists.md), for $C_L(w)$

## Proof depends on

Its proof uses the steps listed in the expansion note, and:

- [Hodge–Tate weights of a locally algebraic character given by one embedding](hodge-tate-weights-of-a-character-given-by-one-embedding.md), for the characters of a finite Galois extension of $\mathbb{Q}_p$ containing $K$ and $L$ to which Conrad's proof reduces
- [Sen's theorem on C-admissible representations](sen-theorem-on-c-admissible-representations.md), for a character trivial near $1$ through $r_L$, such as $(\prod_i \psi_i^{n_i})/\psi$ in Conrad's proof, which has finite image on inertia and so all Hodge–Tate weights $0$
- [Tate–Sen theorem on the Galois cohomology of C(i)](../tate-sen-theorem.md), for $C_L(i)^{G_L} = 0$ when $i \ne 0$, which makes the weights $w_\sigma$ well defined and additive in products
- [Local class field theory: functoriality and explicit reciprocity](../../../../p-adic-numbers/local-class-field-theory-functoriality.md), for the norm functoriality of the local Artin map (its item 1), through which Conrad computes $\psi \circ \mathrm{res}_{F'/L} \circ r_{F'}$ as $\psi \circ r_L \circ N_{F'/L}$

## Sources

- B. Conrad, "Lifting global representations with local properties", preprint dated December 11, 2011,
  <https://math.stanford.edu/~conrad/papers/locchar.pdf>: Appendix B, pp. 32–34: the arithmetic normalization of $r_L$ (p. 32); the
  decomposition of $C_L \otimes_{\mathbb{Q}_p} V$ into lines $V_\sigma = C_L(w_\sigma)$ and (B.1) (p. 33); Proposition
  B.3, p. 33 ("for each $\mathbb{Q}_p$-embedding $\sigma \colon K \to C_L$ the Hodge–Tate weight $w_\sigma$ is equal
  to $n_i$ for the unique $i$ such that the $L$-algebra map $\sigma \otimes 1 \colon K \otimes_{\mathbb{Q}_p} L \to C_L$
  extending $\sigma$ factors through $q_i$"), with its proof, pp. 33–34, which reduces to the characters of the
  one-embedding page, citing J.-P. Serre, *Abelian l-adic representations and elliptic curves*, III, A.5, Theorem 2
  (not read here), and uses that restriction to $G_{F'}$ "has no effect on Hodge–Tate weights" (p. 34).
- O. Brinon and B. Conrad, *CMI summer school notes on p-adic Hodge theory* (preliminary version),
  <https://math.stanford.edu/~conrad/papers/notes.pdf>: Theorem 2.4.6, p. 20 ("for any finite extension $K'/K$
  inside of $\overline{K}$, an object $W$ in $\mathrm{Rep}_{C_K}(G_K)$ is Hodge–Tate if and only iff it is Hodge–Tate when
  viewed in $\mathrm{Rep}_{C_K}(G_{K'})$", with $K' \otimes_K D_K(W) \cong D_{K'}(W)$ as graded spaces).
