# Radford's theorem: the shuffle algebra is a polynomial algebra on the Lyndon words

Let $A$ be a totally ordered alphabet, $A^*$ the free monoid of words over $A$, ordered
lexicographically, and $\mathbb{Q}\langle A \rangle$ the $\mathbb{Q}$-vector space with basis $A^*$. The
shuffle product $\sqcup\!\sqcup$ is the bilinear product defined on words by
$1 \sqcup\!\sqcup u = u \sqcup\!\sqcup 1 = u$ for the empty word $1$ and
$(au) \sqcup\!\sqcup (bv) = a\,(u \sqcup\!\sqcup bv) + b\,(au \sqcup\!\sqcup v)$ for letters $a, b$ and
words $u, v$; it makes $\mathbb{Q}\langle A \rangle$ a commutative and associative algebra, the shuffle
algebra. Let $L$ be the set of [Lyndon words](is-lyndon-word.md). Then the Lyndon words form a
transcendence basis of the shuffle algebra: the homomorphism of commutative $\mathbb{Q}$-algebras from the
polynomial algebra $\mathbb{Q}[L]$ to $(\mathbb{Q}\langle A \rangle, \sqcup\!\sqcup)$ that sends each
Lyndon word to itself is an isomorphism.

More precisely, every word $w$ factors uniquely as a concatenation $w = l_1^{i_1} \cdots l_k^{i_k}$ of
Lyndon words $l_1 > \dots > l_k$ with $i_1, \dots, i_k \ge 1$, and

$$\frac{1}{i_1! \cdots i_k!} \, l_1^{\sqcup\!\sqcup i_1} \sqcup\!\sqcup \cdots \sqcup\!\sqcup l_k^{\sqcup\!\sqcup i_k} = w + \sum_{u < w} \alpha_u u$$

with natural numbers $\alpha_u$, where $l^{\sqcup\!\sqcup i}$ is the $i$-th shuffle power. By this
triangularity the left-hand sides form a $\mathbb{Z}$-basis of the integral shuffle algebra
$\mathbb{Z}\langle A \rangle$ (Melançon and Reutenauer, Corollary of Section 4). Since the shuffle product
has integer structure constants, the isomorphism extends to the shuffle algebra over any field of
characteristic $0$ by extension of scalars (this remark is not in the source).

Melançon and Reutenauer derive the theorem from their description of the basis dual to the
Poincaré–Birkhoff–Witt basis built on the Lyndon basis of the free Lie algebra (their Theorem 2(iii)),
with the unique factorization of words into nonincreasing Lyndon words (Lothaire, Theorem 5.1.5) and
the leading term of the standard bracketing of a Lyndon word (Lothaire, Lemma 5.3.2).

## Depends on

- [Lyndon word](is-lyndon-word.md)

## Sources

- G. Melançon and C. Reutenauer, *Lyndon words, free algebras and shuffles*, Canad. J. Math. 41
  (1989), 577–591, <https://reutenauer.math.uqam.ca/wp-content/uploads/2024/04/LyndonWordsFreeAlgebras-Shuffles1989.pdf>:
  Section 4, the Theorem (credited to Radford), its proof and the Corollary; the definition of the
  shuffle product in Section 3; the lexicographic order in Section 2.
- D. E. Radford, *A natural ring basis for the shuffle algebra and an application to group schemes*,
  J. Algebra 58 (1979), 432–454, the original source, as cited by Melançon and Reutenauer.
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>) uses this result, over a field of characteristic $0$, as
  `GlobalTheory.Published.RadfordShufflePolynomial`.
