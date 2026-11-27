# Global-ontology satisfiability for modal ALCO with the universal role is undecidable

With constant domains, concept satisfiability under a global ontology is undecidable for the modal free description logics $\mathsf{K}^n_{\mathcal{ALCO}_u}$, $n \geq 1$, and $\mathsf{S5}^n_{\mathcal{ALCO}_u}$, $n \geq 2$, where individual names are non-rigid; with expanding domains some of these logics become decidable.

**Theorem (Artale, Kontchakov, Mazzullo and Wolter).** Concept satisfiability under global ontology, with constant domains, is undecidable for [$\mathsf{S5}^n_{\mathcal{ALCO}_u}$](modal-free-description-logics-with-non-rigid.md) for every $n \geq 2$, and for $\mathsf{K}^n_{\mathcal{ALCO}_u}$ for every $n \geq 1$: no algorithm decides, given a concept $C$ and an ontology $\mathcal{O}$, whether some constant-domain interpretation based on a frame of the class satisfies $\mathcal{O}$ and $C$.

The language here has nominals and the universal role but no definite descriptions, and individual names need not designate the same object, or any object, in every world. The source shows that with expanding domains several logics that are undecidable with constant domains become decidable, though Ackermann-hard.

## Depends on

- [Modal free description logics with non-rigid designators](modal-free-description-logics-with-non-rigid.md)

## Proof depends on

None.

## Expansion

The proof reduces from the one-variable first-order modal logic with the "elsewhere" quantifier, $\mathcal{ML}^n_{\mathrm{Diff}}$, whose satisfiability under global ontology over constant-domain models based on $\mathsf{K}^n$ frames, $n \geq 1$, is undecidable by work of Hampson and Kurucz. The reduction theorem of the source shows that, for any class of frames and with both constant and expanding domains, satisfiability of $\mathcal{ML}^n_{\mathrm{Diff}}$-concepts under global ontology is polynomial-time reducible to satisfiability of $\mathcal{ML}^n_{\mathcal{ALCO}_u}$-concepts under global ontology, and conversely with a double-exponential reduction. The case $\mathsf{S5}^n$ with $n \geq 2$ is obtained in the same way from the corresponding undecidability for products of $\mathsf{S5}$ logics.

## Sources

- A. Artale, R. Kontchakov, A. Mazzullo and F. Wolter, "Non-rigid designators in modal and temporal free description logics", in *Proceedings of the 21st International Conference on Principles of Knowledge Representation and Reasoning (KR 2024)*, 2024, pp. 82–93, doi:10.24963/kr.2024/8; read as arXiv:2405.07656v2 (extended version), <https://arxiv.org/abs/2405.07656v2>: the theorem on concept satisfiability under global ontology (label thm:k:global:sat) in the section "Reasoning in Modal Free Description Logics", the reduction theorem for $\mathcal{ML}^n_{\mathrm{Diff}}$ (label th:diff) in the section "Non-Rigid Designators and Counting", and the abstract (undecidability with constant domains, decidability with expanding domains).
