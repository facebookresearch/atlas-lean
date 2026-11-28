# Global consequence for K × K is undecidable

The global consequence relation of the two-dimensional product logic $\mathbf{K} \times \mathbf{K}$ is undecidable, although validity in $\mathbf{K} \times \mathbf{K}$ is decidable.

**Theorem (Marx).** It is undecidable, given bimodal formulas $\varphi$ and $\psi$, whether $\psi$ is a global consequence of $\varphi$ in $\mathbf{K} \times \mathbf{K}$, that is, whether $\psi$ is true throughout every model in which $\varphi$ and every formula of $\mathbf{K} \times \mathbf{K}$ are true throughout (see [products and commutators of modal logics](products-and-commutators-of-modal-logics.md)). Since $\mathbf{K} \times \mathbf{K}$ is globally Kripke complete, as the source notes, this is the same as $\psi$ being true throughout every model based on a product frame $\mathfrak{F}_1 \times \mathfrak{F}_2$ in which $\varphi$ is true throughout. Marx states the result as Theorem 2.4 (global satisfaction) and Corollary 2.5 (global consequence) of his paper, writing $\mathbf{K}^2$ for $\mathbf{K} \times \mathbf{K}$.

Validity in $\mathbf{K} \times \mathbf{K}$ is decidable (Gabbay and Shehtman), but not in elementary time. The global consequence relation of $\mathbf{K} \times \mathbf{S5}$ is decidable, in co2NEXPTIME.

## Depends on

- [products and commutators of modal logics](products-and-commutators-of-modal-logics.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The tiling problem is undecidable](../../../../TheoryOfComputation/undecidable-problems/wang-tiles/the-tiling-problem-is-undecidable.md)

## Expansion

The copy read attributes the result to a reduction of the $\omega \times \omega$ tiling problem, without details: global consequence lets $\varphi$ act as an axiom throughout the product model, which is what such grid encodings need. A finite tile set tiles the $\omega \times \omega$ quadrant exactly when it tiles every finite square, which by the compactness statement of the linked page holds exactly when it tiles the plane. A good expansion gives Marx's reduction in full.

## Sources

- M. Marx, "Complexity of products of modal logics", *Journal of Logic and Computation* 9(2):197–214, 1999, doi:10.1093/logcom/9.2.197; read in the author's copy at <https://staff.fnwi.uva.nl/m.j.marx/pub/products.pdf>: Section 1 ($\mathbf{K}^2 = \mathbf{K} \times \mathbf{K}$), Theorem 2.4 and Corollary 2.5.
- C. Hampson, S. Kikot and A. Kurucz, "The decision problem of modal product logics with a diagonal, and faulty counter machines", *Studia Logica* 104(3):455–486, 2016, doi:10.1007/s11225-015-9647-7; read in the authors' open-access copy at <https://kuag19.github.io/homepage/diagundec.pdf>: Section 2 (the definition of global consequence), the proof of Corollary 1 in Section 3 (the remark on the tiling reduction) and Table 1 in Section 1 (global $\mathbf{K} \times \mathbf{K}$-consequence undecidable, validity of $\mathbf{K} \times \mathbf{K}$ and global $\mathbf{K} \times \mathbf{S5}$-consequence).
