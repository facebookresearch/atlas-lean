# Derivability in Morrill's bracketed calculi with a subexponential is undecidable

Derivability is undecidable in both of Morrill's categorial calculi that combine brackets with a subexponential and bracket-aware contraction, already in their fragments without additive connectives.

**Theorem (Kanovich, Kuznetsov and Scedrov).** For the [calculi of Morrill](morrill-s-calculi-with-brackets-and-a.md):

1. the derivability problem for ${!}^{2015}_{\mathbf b}\mathbf{L}^{*}\mathbf{b}(\mathrm{st})$ is undecidable;
2. the derivability problem for ${!}^{2018}_{\mathbf b}\mathbf{L}^{*}\mathbf{b}(\mathrm{st})$ is undecidable

(the two theorems on the original systems in Section 9 of arXiv:2008.00075v2). The input is a sequent. Since these calculi have no cut rule, the systems ${!}^{2015}_{\mathbf b}\mathbf{MALC}^{*}\mathbf{b}(\mathrm{st})$ and ${!}^{2018}_{\mathbf b}\mathbf{MALC}^{*}\mathbf{b}(\mathrm{st})$ with additives, and Morrill's larger systems containing them, are conservative over these fragments and have undecidable derivability as well.

The source proves the same for the modified versions of these calculi with cut elimination, and for one-division fragments of several of them (Section 11).

## Depends on

- [Morrill's calculi with brackets and a subexponential](morrill-s-calculi-with-brackets-and-a.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Reachability for string rewriting is undecidable](../../../TheoryOfComputation/undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-sr.md)

## Expansion

The proof encodes derivability $\Rightarrow^*_S$ in a semi-Thue system $S$ (one-directional string rewriting), for a fixed $S$ whose derivability relation is undecidable (Markov and Post; Theorem 3 of the source); the encoding is computable from $S$ as well, so undecidability of reachability for string rewriting with $S$ part of the input also suffices: following Buszkowski, a rule $x_1 \cdots x_k \Rightarrow y_1 \cdots y_m$ becomes the hypothesis $y_1, \dots, y_m \to x_1 \cdot \ldots \cdot x_k$, and $a_1, \dots, a_n \to b_1 \cdot \ldots \cdot b_k$ is derivable from these hypotheses in the Lambek calculus iff $b_1 \cdots b_k \Rightarrow^* a_1 \cdots a_n$. Each calculus *internalizes* finite sets of Lambek formulas: the hypotheses can be placed, under ${!}$, into the stoup and copied by contraction wherever needed, using brackets that are erased again by the bracket modalities. Undecidability then follows from a generic theorem for calculi that are sound for a bracket-forgetting projection into the Lambek calculus with exponential and internalize finite sets of formulas. For the 2018 calculus the left ${!}$-rule is not invertible, which requires a separate key lemma.

## Sources

- M. Kanovich, S. Kuznetsov and A. Scedrov, "The multiplicative-additive Lambek calculus with subexponential and bracket modalities", *Journal of Logic, Language and Information* 30:31–88, 2021, doi:10.1007/s10849-020-09320-9; read as arXiv:2008.00075v2, <https://arxiv.org/abs/2008.00075v2>: Section 9 ("Undecidability", the theorems for the original systems and the generic undecidability theorem) and Section 11 ("Undecidability for one-division fragments") of arXiv:2008.00075v2.
