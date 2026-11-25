# POTVirtual Pullback

The virtual class of a cone presentation `F` that is an obstruction theory
(`IsObstructionTheory`), for a Noetherian $\mathbb{C}$-algebra $B$ and a presentation `P` of $B$ as
a quotient of a $\mathbb{C}$-algebra `P.Ring` (`Algebra.Extension ℂ B`) that is isomorphic to a
polynomial ring over $\mathbb{C}$ in finitely many variables: the class `classFromCone F D J` in the
rational Chow group of $\operatorname{Spec} B$ in degree `F.zeroRank - F.negativeRank`, the
zero-section pullback, through the given `D` and `J`, of the fundamental class of the cone image in
degree `F.zeroRank`.
