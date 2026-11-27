# Associative modal logics valid on the union frame are undecidable

Every associative normal modal logic contained in the logic of the frame of all subsets of the natural numbers under union is undecidable; equivalently, every variety of associative BAOs containing the complex algebra of this frame has an undecidable equational theory.

**Theorem (Knudstorp).** Let $\mathbf L$ be an [associative normal modal logic](associative-normal-modal-logic.md), that is, $\mathbf{AK}_2 \subseteq \mathbf L$, such that $\mathbf L \subseteq \mathrm{Log}(\mathcal P(\mathbb N), \cup)$. Then $\mathbf L$ is undecidable: there is no algorithm that decides, given an $\mathcal L$-formula $\varphi$, whether $\varphi \in \mathbf L$. Equivalently, if a variety $\mathsf V$ of associative BAOs contains $(\mathcal P(\mathbb N), \cup)^+$, then the equational theory of $\mathsf V$ is undecidable.

The same holds with $(\mathcal P(\mathbb N), \cup)$ replaced by $(\mathcal P(\mathbb N), \uplus)$, the partial operation with $X = Y \uplus Z$ iff $X = Y \cup Z$ and $Y \cap Z = \emptyset$ (Theorem 3.16 of the source), and by $(\mathcal P(\mathbb N) \setminus \{\emptyset\}, \cup)$ (Theorem 3.19). Since $\mathbf{AK}_2 \subseteq \mathrm{Log}(\mathcal P(\mathbb N), \cup)$, the theorem includes the undecidability of $\mathbf{AK}_2$ itself, first proved by Kurucz, Németi, Sain and Simon by a reduction from the Post correspondence problem.

## Depends on

- [Associative normal modal logic](associative-normal-modal-logic.md)

## Proof depends on

- [The tiling problem is undecidable](../../../TheoryOfComputation/undecidable-problems/wang-tiles/the-tiling-problem-is-undecidable.md)

## Expansion

The proof reduces the tiling problem for the quadrant $\mathbb N^2$ (Berger), which is equivalent to tiling the plane by a compactness argument. For each finite set $W$ of Wang tiles one computes an $\mathcal L$-formula $\varphi_W$ (Definition 4.3) and proves two lemmas: if $W$ does not tile $\mathbb N^2$, then $\varphi_W \in \mathbf{AK}_2$, i.e. $\varphi_W$ is valid on every associative frame (Lemma 3.3); and if $\varphi_W$ is valid on $(\mathcal P(\mathbb N), \cup)$, then $W$ does not tile $\mathbb N^2$ (Lemma 3.4), so that a tiling yields a refuting valuation on this single frame. Associativity of the ternary relation is what makes the two ways of composing a horizontal and a vertical step meet, as the edges of a grid square do (Remark 4.1). Hence for every $\mathbf L$ between $\mathbf{AK}_2$ and $\mathrm{Log}(\mathcal P(\mathbb N), \cup)$, $\varphi_W \in \mathbf L$ iff $W$ does not tile the quadrant.

## Sources

- S. B. Knudstorp, "Diamonds and dominoes: impossibility results for associative modal logics", *The Journal of Symbolic Logic*, published online 2026, pp. 1–26, <https://doi.org/10.1017/jsl.2026.10256>; numbers from arXiv:2506.16366v2, <https://arxiv.org/abs/2506.16366v2>: Theorem 3.5 with Lemmas 3.3 and 3.4, Definition 4.3, Theorems 3.11, 3.16 and 3.19.
- Á. Kurucz, I. Németi, I. Sain and A. Simon, "Decidable and undecidable logics with a binary modality", *Journal of Logic, Language and Information* 4(3):191–206, 1995, <https://doi.org/10.1007/BF01049412>: undecidability of $\mathbf{AK}_2$; not read directly here: this clause rests on its statement in the arXiv copy of the first source above (Section 1 and Theorem 3.11).
