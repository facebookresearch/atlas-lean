# Every modal logic between Kⁿ and S5ⁿ is undecidable and not finitely axiomatizable for n ≥ 3

For every $n \geq 3$, every set of $n$-modal formulas between the product logics $\mathbf{K}^n$ and $\mathbf{S5}^n$ is undecidable and not finitely axiomatizable; in particular $\mathbf{K} \times \mathbf{K} \times \mathbf{K}$ is undecidable although it has the finite model property.

**Theorem (Hirsch, Hodkinson and Kurucz).** Let $n \geq 3$ and let $L$ be any set of $n$-modal formulas with $\mathbf{K}^n \subseteq L \subseteq \mathbf{S5}^n$ (see [products and commutators of modal logics](products-and-commutators-of-modal-logics.md)). Then $L$ is undecidable (Theorem 1) and not finitely axiomatizable (Theorem 3).

$\mathbf{K}^n$ has the finite model property for every $n$ (Gabbay and Shehtman), so $\mathbf{K}^3$ is an example of an undecidable but recursively enumerable logic with the finite model property.

## Depends on

- [products and commutators of modal logics](products-and-commutators-of-modal-logics.md)

## Proof depends on

- [It is undecidable whether a finite frame is a frame for a logic between Kⁿ and S5ⁿ](frame-problem-for-logics-between-kn-and-s5n.md)

## Expansion

The proof reduces the undecidable problem whether a finite simple relation algebra is representable (Hirsch and Hodkinson): from such an algebra $\mathcal{A}$ one builds a finite $n$-frame $\mathfrak{F}_{\mathcal{A},n}$ and a $3$-modal formula $\varphi_{\mathcal{A}}$ such that, for every $L$ in the interval, $\mathfrak{F}_{\mathcal{A},n}$ is a frame for $L$ iff $\neg\varphi_{\mathcal{A}} \notin L$ iff $\mathfrak{F}_{\mathcal{A},3}$ is a p-morphic image of a universal product $\mathbf{S5}^3$-frame, and the last condition holds iff $\mathcal{A}$ is representable (Lemmas 5 and 6). A good expansion links a page for the undecidability of representability of finite relation algebras, which has none yet.
Non-finite axiomatizability follows from the undecidability of the frame problem: a finite axiomatization would give a test for finite frames.

## Sources

- R. Hirsch, I. Hodkinson and A. Kurucz, "On modal logics between K × K × K and S5 × S5 × S5", *Journal of Symbolic Logic* 67(1):221–234, 2002, doi:10.2178/jsl/1190150040; read in the authors' open-access copy at <https://www.doc.ic.ac.uk/~imh/papers/k3undec.pdf>: Section 1, Theorems 1 and 3 and the derivation of Theorem 3 from Theorem 2.
- A. Kurucz, "Combining modal logics", in P. Blackburn, J. van Benthem and F. Wolter (eds.), *Handbook of Modal Logic*, Studies in Logic and Practical Reasoning 3, Elsevier, 2007, pp. 869–924, doi:10.1016/S1570-2464(07)80018-8; read in the author's open-access copy at <https://kuag19.github.io/homepage/combi.pdf>: Theorems 40 and 42.
