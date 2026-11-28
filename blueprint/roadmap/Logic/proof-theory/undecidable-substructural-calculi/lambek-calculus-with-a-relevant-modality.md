# Lambek calculus with a relevant modality

The calculus ${!}\mathbf{L}^*$ extends the Lambek calculus with empty antecedents and the two divisions by one modality ${!}$ that allows contraction and permutation of the formulas it marks, but not weakening.

**Formulas** are built from variables (primitive types) with the divisions $/$ and $\backslash$ and the unary ${!}$. Sequents are $\Pi \to A$ with $\Pi$ a finite, possibly empty, ordered sequence of formulas.

**Rules.** The axiom $A \to A$; the Lambek rules

$$
\frac{\Gamma \to A \quad \Delta_1, B, \Delta_2 \to C}{\Delta_1, B / A, \Gamma, \Delta_2 \to C}, \quad \frac{\Gamma, A \to B}{\Gamma \to B / A}, \quad \frac{\Gamma \to A \quad \Delta_1, B, \Delta_2 \to C}{\Delta_1, \Gamma, A \backslash B, \Delta_2 \to C}, \quad \frac{A, \Gamma \to B}{\Gamma \to A \backslash B};
$$

dereliction $\Gamma_1, A, \Gamma_2 \to C \,/\, \Gamma_1, {!}A, \Gamma_2 \to C$; promotion ${!}A_1, \dots, {!}A_n \to B \,/\, {!}A_1, \dots, {!}A_n \to {!}B$; permutation of ${!}A$ past any sequence $\Gamma$ in either direction; and contraction $\Delta_1, {!}A, {!}A, \Delta_2 \to C \,/\, \Delta_1, {!}A, \Delta_2 \to C$. There is no weakening and the cut rule is not included. ${!}\mathbf{L}^*_{/}$ is the fragment with only $/$ and ${!}$; by the subformula property it is a conservative fragment.

## Depends on

- [Derivability in the Lambek calculus](../../../TheoryOfComputation/np-completeness/strings-and-puzzles/lambek-calculus-derivability/derivable.md)

## Proof depends on

None.

## Expansion

The system was introduced by Morrill and Valentín as a conservative fragment of their larger categorial calculus $\mathbf{Db}{!}{?}$, to model linguistic phenomena such as parasitic gaps. Unlike the Lambek calculus of the linked page, it has no product and allows empty antecedents. It is the special case of the Lambek calculus with subexponentials with a single label allowing contraction and exchange but not weakening, restricted to the divisions.

## Sources

- M. Kanovich, S. Kuznetsov and A. Scedrov, "Undecidability of the Lambek calculus with a relevant modality", in *Formal Grammar 2015/2016*, Lecture Notes in Computer Science 9804, Springer, 2016, pp. 240–256, doi:10.1007/978-3-662-53042-9_14; read as arXiv:1601.06303v4, <https://arxiv.org/abs/1601.06303v4>: Section 1 (the calculus ${!}\mathbf{L}^*$ and its fragments).
