# It is undecidable whether a finite frame is a frame for a logic between Kⁿ and S5ⁿ

For every $n \geq 3$ and every set of $n$-modal formulas between $\mathbf{K}^n$ and $\mathbf{S5}^n$, it is undecidable whether a given finite frame is a frame for it, and the set lacks the product finite model property in a strong sense.

**Theorem (Hirsch, Hodkinson and Kurucz).** Let $n \geq 3$ and let $L$ be any set of $n$-modal formulas with $\mathbf{K}^n \subseteq L \subseteq \mathbf{S5}^n$ (see [products and commutators of modal logics](products-and-commutators-of-modal-logics.md)).

1. It is undecidable whether a finite $n$-frame is a frame for $L$, that is, validates every formula of $L$ (Theorem 2).
2. There is a $3$-modal formula that does not belong to $L$ but is valid in all finite $k$-ary product frames, for all $k \geq 3$; so $L$ lacks the product finite model property (Theorem 4).

## Depends on

- [products and commutators of modal logics](products-and-commutators-of-modal-logics.md)

## Proof depends on

None.

## Expansion

The proof reduces the undecidable problem whether a finite simple relation algebra is representable (Hirsch and Hodkinson): from such an algebra $\mathcal{A}$ one builds a finite $n$-frame $\mathfrak{F}_{\mathcal{A},n}$ and a $3$-modal formula $\varphi_{\mathcal{A}}$ such that, for every $L$ in the interval, $\mathfrak{F}_{\mathcal{A},n}$ is a frame for $L$ iff $\neg\varphi_{\mathcal{A}} \notin L$ iff $\mathfrak{F}_{\mathcal{A},3}$ is a p-morphic image of a universal product $\mathbf{S5}^3$-frame, and the last condition holds iff $\mathcal{A}$ is representable (Lemmas 5 and 6). Clause 2 applies the same lemmas to a finite simple relation algebra that is representable only on an infinite base, such as Maddux's point algebra. A good expansion links pages for the undecidability of representability of finite relation algebras and for such an algebra; neither has a page yet.

## Sources

- R. Hirsch, I. Hodkinson and A. Kurucz, "On modal logics between K × K × K and S5 × S5 × S5", *Journal of Symbolic Logic* 67(1):221–234, 2002, doi:10.2178/jsl/1190150040; read in the authors' open-access copy at <https://www.doc.ic.ac.uk/~imh/papers/k3undec.pdf>: Section 1, Theorems 2 and 4, and Section 3 (proof of Theorem 4).
- A. Kurucz, "Combining modal logics", in P. Blackburn, J. van Benthem and F. Wolter (eds.), *Handbook of Modal Logic*, Studies in Logic and Practical Reasoning 3, Elsevier, 2007, pp. 869–924, doi:10.1016/S1570-2464(07)80018-8; read in the author's open-access copy at <https://kuag19.github.io/homepage/combi.pdf>: Theorem 25.
