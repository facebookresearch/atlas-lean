# RNA design extension is NP-complete in the Watson–Crick model

**Setting.** An RNA sequence is a word over $\{A,C,G,U\}$; a pseudoknot-free secondary structure of length $n$ is a well-parenthesized word over $\{(,),\cdot\}$, matching parentheses being paired bases. In the **Watson–Crick energy model**, a sequence folds into the structures that maximize the number of nested pairs, where only complementary pairs $A$–$U$ and $C$–$G$ may pair. A target structure $S$ is **designable** if some sequence has $S$ as its unique optimal structure. **RNA Design Extension**: given $S$ and a partial labeling prescribing the bases at some positions (the constraints used by design software and by the EteRNA project), decide whether the labeling extends to a sequence whose unique optimal fold is $S$.

**Theorem.**
1. RNA Design Extension is NP-complete.
2. It can be solved in time $\sqrt3^{\,n}\,n^{O(1)}$, and in time $2^s\,n^{O(1)}$ where $s$ is the number of unlabeled positions, both in polynomial space.

By contrast, predicting the optimal pseudoknot-free fold of a given sequence takes cubic time (and truly subcubic time is possible), so with base constraints design is strictly harder than prediction unless $\mathrm{P}=\mathrm{NP}$; the complexity of unconstrained design in this model was a long-standing open question.

## Expansion

Membership in NP: given a candidate sequence, checking that $S$ is its unique maximum-pairing fold is a polynomial dynamic program. Hardness is a reduction from a variant of 3-SAT built from arches of parentheses of different widths and a linear order interleaving variable and clause gadgets; the prescribed bases force the gadgets, and a rematching strategy increases the number of pairs exactly when the three literals of some clause are all false, so $S$ is the unique optimum iff the formula is satisfiable. For the exponential algorithms, designable structures avoid two forbidden families of local motifs ($m_5$ and $m_{3\circ}$, from earlier work of Haleš et al.), which bounds the branching of the structure tree; for instance the virtual root has at most four children, and a search over labelings of the tree then gives the stated bounds.

## Sources

- Édouard Bonnet, Paweł Rzążewski and Florian Sikora, "Designing RNA Secondary Structures is Hard", arXiv:1710.11513 (2017), main theorem (NP-completeness of RNA Design Extension), the quoted forbidden-motif theorem and the exact-algorithm theorem, <https://doi.org/10.48550/arXiv.1710.11513>.
