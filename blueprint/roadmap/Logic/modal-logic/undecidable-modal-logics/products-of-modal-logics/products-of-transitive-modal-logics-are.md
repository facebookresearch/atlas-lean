# Products of transitive modal logics are undecidable

Every Kripke complete bimodal logic that contains the product of two copies of K4 and has product frames of arbitrarily large finite or infinite depth is undecidable; in particular $\mathbf{K4} \times \mathbf{K4}$, a finitely axiomatizable logic, is undecidable.

**Theorem (Gabelaia, Kurucz, Wolter and Zakharyaschev).** Let $L$ be a Kripke complete bimodal logic with $\mathbf{K4} \times \mathbf{K4} \subseteq L$ whose frames include product frames of arbitrarily large finite or infinite cluster-depth (see [products and commutators of modal logics](products-and-commutators-of-modal-logics.md)). Then $L$ is undecidable.

Since $\mathbf{K4} \times \mathbf{K4} = [\mathbf{K4}, \mathbf{K4}]$, it is a finitely axiomatizable but undecidable logic. The theorem covers products of standard transitive logics such as $\mathbf{K4} \times \mathbf{K4}$, $\mathbf{S4} \times \mathbf{S4}$, $\mathbf{GL} \times \mathbf{GL}$ and $\mathbf{Grz} \times \mathbf{Grz}$. By contrast, products with an $\mathbf{S5}$ or $\mathbf{K}$ component are often decidable, and versions with expanding domains, such as the expanding product of $\mathbf{GL.3}$ and $\mathbf{GL}$, can be decidable although the product is not.

## Depends on

- [products and commutators of modal logics](products-and-commutators-of-modal-logics.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The source of the copy read sketches the proof: the $\omega \times \omega$ grid is represented in product frames of large depth by an enumeration of its points along chains of the two transitive relations, and an undecidable $\omega \times \omega$ tiling problem is reduced to satisfiability. A good expansion links the undecidability of the $\omega \times \omega$ tiling problem in the form the proof uses, with the grid built from an enumeration of pairs.

## Sources

- D. Gabelaia, A. Kurucz, F. Wolter and M. Zakharyaschev, "Products of 'transitive' modal logics", *Journal of Symbolic Logic* 70(3):993–1021, 2005, doi:10.2178/jsl/1122038925 (original source, cited beside the copy read).
- A. Kurucz, "Combining modal logics", in P. Blackburn, J. van Benthem and F. Wolter (eds.), *Handbook of Modal Logic*, Studies in Logic and Practical Reasoning 3, Elsevier, 2007, pp. 869–924, doi:10.1016/S1570-2464(07)80018-8; read in the author's open-access copy at <https://kuag19.github.io/homepage/combi.pdf>: Theorem 34(ii), the remark following it, and the discussion of its proof in Section 3.4.
- D. Gabelaia, A. Kurucz, F. Wolter and M. Zakharyaschev, "Non-primitive recursive decidability of products of modal logics with expanding domains", *Annals of Pure and Applied Logic* 142(1–3):245–268, 2006, doi:10.1016/j.apal.2006.01.001; read in the authors' open-access copy at <http://titan.dcs.bbk.ac.uk/~michael/expand.pdf>: Section 1 (the product of $\mathbf{GL.3}$ and $\mathbf{GL}$ versus its expanding version).
