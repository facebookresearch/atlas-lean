# VC dimension is at most Littlestone dimension and mistake-bound comparisons

Let $C$ be a class of functions $X \to Y$. Then $\mathrm{Ndim}(C) \le \mathrm{Ldim}(C)$; for Boolean classes this gives $\mathrm{VCdim}(C) \le \mathrm{Ldim}(C) = \mathrm{opt}(C)$. In particular infinite Natarajan or VC dimension forces infinite Littlestone dimension.

## Proof sketch

A Natarajan-shattered set $\{w_1, \ldots, w_d\}$ with witness functions $f_0, f_1$ gives a complete mistake tree of depth $d$ querying $w_j$ at depth $j$ with labels $f_0(w_j) \ne f_1(w_j)$. The same inequality follows from the chain of Brukhim et al. and Hanneke et al.: the Natarajan dimension is at most the DS dimension (a copy of the Boolean cube $\prod_j \{f_0(w_j), f_1(w_j)\}$ is a pseudo-cube), the DS dimension is at most the level-constrained Littlestone dimension (the largest depth of a shattered mistake tree whose internal nodes on each level carry the same instance), and that is at most the Littlestone dimension. For Boolean classes the Natarajan dimension is the VC dimension and $\mathrm{Ldim}(C) = \mathrm{opt}(C)$ is Littlestone's theorem.

Domain-size bound (derived; no cited source states it): if $X$ is finite, $\mathrm{Ldim}(C) \le |X|$ for every label set $Y$. Along any path of a mistake tree, an instance queried at an ancestor has a fixed label in the whole subtree below the edge taken, so it cannot be queried again with two distinct realizable labels; the instances on a root-to-leaf path are therefore distinct, and the depth is at most $|X|$. Equality holds for the class of all functions $X \to Y$ whenever $|Y| \ge 2$, realized by the tree querying the points of $X$ in order, so this bound improves on the halving bound $\lfloor\log_2 |Y|^{|X|}\rfloor$ when $|Y| \ge 3$ and $|X| \ge 2$.

## Depends on

- [Littlestone's theorem for arbitrary label sets: optimal mistake bound equals the multiclass Littlestone dimension](multiclass-littlestone-theorem.md)
- [N-shattering](../../pac-learning/sample-complexity-and-combinatorial-dimensions/natarajan-dimension-and-the-natarajan-lemma/nshatters.md)

## Sources

- Amit Daniely, Sivan Sabato, Shai Ben-David and Shai Shalev-Shwartz, "Multiclass Learnability and the ERM Principle", Journal of Machine Learning Research, 2015.
- Nick Littlestone, "Learning Quickly When Irrelevant Attributes Abound: A New Linear-Threshold Algorithm", Machine Learning 2(4), 1988, Theorem 4.
- S. Shalev-Shwartz and S. Ben-David, "Understanding Machine Learning: From Theory to Algorithms", Cambridge University Press, 2014, Theorem 21.9.
- N. Brukhim, D. Carmon, I. Dinur, S. Moran and A. Yehudayoff, "A Characterization of Multiclass Learnability", Proceedings of the 63rd IEEE Symposium on Foundations of Computer Science (FOCS), 2022, Section 2.
- S. Hanneke, V. Raman, A. Shaeiri and U. Subedi, "Multiclass Transductive Online Learning", Advances in Neural Information Processing Systems 37 (NeurIPS), 2024, Proposition 1 and Appendix F.2, Proposition 2.
