# Locally algebraic characters of local Galois groups

Let $L$ and $K$ be finite extensions of $\mathbb{Q}_p$ and let
$\psi \colon G_L^{\mathrm{ab}} \to K^\times$ be a continuous character, viewed also as a character of $G_L$. Let
$r_L \colon L^\times \to G_L^{\mathrm{ab}}$ be the [local Artin map](../../../../p-adic-numbers/local-class-field-theory.md)
of $L$, in either normalization. Let $K \otimes_{\mathbb{Q}_p} L = \prod_i F_i$ be the decomposition into
fields, with quotient maps $q_i \colon K \otimes_{\mathbb{Q}_p} L \to F_i$; each $F_i$ is a finite extension of
$K$ and of $L$. The character $\psi$ is **locally algebraic** if there is a homomorphism of algebraic groups over $\mathbb{Q}_p$
$r \colon R_{L/\mathbb{Q}_p}(\mathbb{G}_m) \to \mathrm{GL}_K$, from the Weil restriction of scalars of $\mathbb{G}_m$ to the
linear group of $K$ as a $\mathbb{Q}_p$-vector space, such that $\psi(r_L(x)) = r(x^{-1})$ for all $x \in L^\times$ close
enough to $1$. Then $r$ is unique, since every nonempty open subset of $L^\times$ is Zariski dense in
$R_{L/\mathbb{Q}_p}(\mathbb{G}_m)$. Equivalently, there are integers $n_i$, one for each factor $F_i$, such that

$$\psi(r_L(x)) = \prod_i N_{F_i/K}\bigl(q_i(1 \otimes x)\bigr)^{-n_i}$$

for all $x$ in some neighbourhood of $1$ in $L^\times$. Whether $\psi$ is locally algebraic does not depend on the
normalization of $r_L$; changing it replaces each $n_i$ by $-n_i$.

The second form follows from Serre's Proposition 2, which applies as $\psi$ is semisimple on inertia, the elements
of $K$ acting on $K$ by commuting semisimple operators: after extending scalars to a finite Galois extension $E$ of
$\mathbb{Q}_p$ that contains all conjugates of $K$ and $L$, the characters $\sigma \circ \psi$, for the embeddings
$\sigma \colon K \to E$, are near $1$ products of the characters $x \mapsto a(x)^{-1}$ for the embeddings
$a \colon L \to E$, and invariance under $\operatorname{Gal}(E/\mathbb{Q}_p)$ makes their exponents depend only on the factor
through which $\sigma \otimes a$ factors (Conrad, Lemma B.2 and (B.1)). Conrad's Definition B.1 asks instead that
$\psi \circ r_L$ agree near $1$ with the map on $\mathbb{Q}_p$-points of a homomorphism
$R_{L/\mathbb{Q}_p}(\mathbb{G}_m) \to R_{K/\mathbb{Q}_p}(\mathbb{G}_m)$; it is the same condition, since inversion is
algebraic and $r$ takes values in the closed subgroup $R_{K/\mathbb{Q}_p}(\mathbb{G}_m)$ of $\mathrm{GL}_K$, which contains
the values of $\psi$. For $L = \mathbb{Q}_p$ there is one factor, $F_1 = K$, and the condition reads
$\psi(r_{\mathbb{Q}_p}(x)) = x^{-n}$ for $x \in \mathbb{Q}_p^\times$ near $1$.

## Depends on

- [Local class field theory: the local Artin map](../../../../p-adic-numbers/local-class-field-theory.md), for $r_L$

## Proof depends on

The definition needs no proof. The uniqueness of $r$ uses only Zariski density; the effect of the normalization
holds because the two normalizations of $r_L$ are inverse to each other; the second form uses Serre's
Proposition 2 and Galois descent, as said after the definition.

## Sources

- J.-P. Serre, *Abelian l-adic representations and elliptic curves*, Advanced Book Classics, Addison-Wesley
  (1989), a reprint of the 1968 edition, whose ground field $K$ is the field $L$ here: Chapter III, §1.1, p. III-2
  (Definition: an abelian $p$-adic representation
  $\rho$ of $K$ in $V$ is locally algebraic "if there is an algebraic morphism $r \colon T \to \mathrm{GL}_V$ such that
  $\rho \circ i(x) = r(x^{-1})$ for all $x \in K^*$ close enough to $1$", with the uniqueness of $r$ by Zariski density,
  and Example 1, the case $K = \mathbb{Q}_p$ of dimension $1$), and Propositions 1 and 2, pp. III-3–4 (Proposition 2:
  after diagonalization over a finite extension $E$ containing all conjugates of $K$, $\rho$ is locally algebraic exactly
  when its characters $\chi_i$ satisfy $\chi_i(u) = \prod_{\sigma} \sigma(u)^{-n_\sigma(i)}$ for $u$ close to $1$).
- B. Conrad, "Lifting global representations with local properties", preprint dated December 11, 2011,
  <https://math.stanford.edu/~conrad/papers/locchar.pdf>: Appendix B, pp. 32–33: Definition B.1 (locally algebraic, with "using either
  normalization" of $r_L$), the products $\prod_\tau \tau(x)^{-n_\tau}$ over the $\mathbb{Q}_p$-embeddings
  $\tau \colon L \to K'$ into a finite extension $K'/K$ that splits $L$, Lemma B.2 (such a product is valued in
  $K$ exactly when $n_\tau$ depends only on the factor field of $K \otimes_{\mathbb{Q}_p} L$ through which
  $1 \otimes \tau$ factors) and (B.1).
