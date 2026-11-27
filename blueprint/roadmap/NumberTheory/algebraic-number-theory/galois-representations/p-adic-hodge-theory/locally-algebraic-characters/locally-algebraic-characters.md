# Locally algebraic characters of local Galois groups

Let $L$ and $K$ be finite extensions of $\mathbb{Q}_p$ and let
$\psi \colon G_L^{\mathrm{ab}} \to K^\times$ be a continuous character, viewed also as a character of $G_L$. Let
$r_L \colon L^\times \to G_L^{\mathrm{ab}}$ be the [local Artin map](../../../../p-adic-numbers/local-class-field-theory.md)
of $L$, in either normalization. Let $K \otimes_{\mathbb{Q}_p} L = \prod_i F_i$ be the decomposition into
fields, with quotient maps $q_i \colon K \otimes_{\mathbb{Q}_p} L \to F_i$; each $F_i$ is a finite extension of
$K$ and of $L$. The character $\psi$ is **locally algebraic** if there are integers $n_i$, one for each
factor $F_i$, such that

$$\psi(r_L(x)) = \prod_i N_{F_i/K}\bigl(q_i(1 \otimes x)\bigr)^{-n_i}$$

for all $x$ in some neighbourhood of $1$ in $L^\times$. Whether $\psi$ is
locally algebraic does not depend on the normalization of $r_L$; changing it replaces each $n_i$ by $-n_i$.

Conrad's definition (Definition B.1) asks for a homomorphism of $\mathbb{Q}_p$-tori
$R_{L/\mathbb{Q}_p}(\mathbb{G}_m) \to R_{K/\mathbb{Q}_p}(\mathbb{G}_m)$ (Weil restrictions of scalars) whose map
on $\mathbb{Q}_p$-points $L^\times \to K^\times$ agrees with $\psi \circ r_L$ near $1$. It is the same
condition: each map above comes from such a homomorphism, since the norms and the $q_i$ are algebraic, and
Conrad shows (Lemma B.2 and (B.1)) that the homomorphism of a locally algebraic $\psi$ has this form. For
$L = \mathbb{Q}_p$ there is one factor, $F_1 = K$, and the condition reads $\psi(r_{\mathbb{Q}_p}(x)) = x^{-n}$
for $x \in \mathbb{Q}_p^\times$ near $1$.

## Depends on

- [Local class field theory: the local Artin map](../../../../p-adic-numbers/local-class-field-theory.md), for $r_L$

## Proof depends on

The definition needs no proof. The effect of the normalization holds because the two normalizations of $r_L$ are
inverse to each other, and the comparison with Conrad's formulation is his Lemma B.2 and (B.1).

## Sources

- B. Conrad, "Lifting global representations with local properties", preprint dated December 11, 2011,
  <https://math.stanford.edu/~conrad/papers/locchar.pdf>: Appendix B, pp. 32–33: Definition B.1 (locally algebraic, with "using either
  normalization" of $r_L$), the products $\prod_\tau \tau(x)^{-n_\tau}$ over the $\mathbb{Q}_p$-embeddings
  $\tau \colon L \to K'$ into a finite extension $K'/K$ that splits $L$, Lemma B.2 (such a product is valued in
  $K$ exactly when $n_\tau$ depends only on the factor field of $K \otimes_{\mathbb{Q}_p} L$ through which
  $1 \otimes \tau$ factors) and (B.1).
- J.-P. Serre, *Abelian l-adic representations and elliptic curves*, Chapter III, Appendix (locally algebraic
  abelian representations), as cited by Conrad, for the theory of locally algebraic representations.
