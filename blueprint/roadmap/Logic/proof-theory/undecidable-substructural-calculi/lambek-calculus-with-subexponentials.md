# Lambek calculus with subexponentials

The multiplicative-additive Lambek calculus with subexponentials $\mathrm{SMALC}_\Sigma$ extends the Lambek calculus with empty antecedents by the additives and by a family of modalities ${!}^s$, each allowing a chosen subset of weakening, contraction and exchange as fixed by a signature $\Sigma$.

**Signatures.** A *subexponential signature* is $\Sigma = \langle \mathcal{I}, \preceq, \mathcal{W}, \mathcal{C}, \mathcal{E} \rangle$ where $\mathcal{I} = \{s_1, \dots, s_n\}$ is a finite set of labels with a preorder $\preceq$, and $\mathcal{W}, \mathcal{C}, \mathcal{E} \subseteq \mathcal{I}$ are upward closed under $\preceq$ and satisfy $\mathcal{W} \cap \mathcal{C} \subseteq \mathcal{E}$. Labels in $\mathcal{W}$, $\mathcal{C}$, $\mathcal{E}$ allow weakening, contraction and exchange respectively.

**Formulas** are built from variables $p_1, p_2, \dots$ and the unit $\mathbf{1}$ with the product $\cdot$, the divisions $\backslash$ and $/$, the additives $\wedge$, $\vee$, and a unary ${!}^s$ for each $s \in \mathcal{I}$. Sequents are $\Gamma \to C$ with $\Gamma$ a finite, possibly empty, ordered sequence.

**Rules.** The axiom $A \to A$; the Lambek rules for $\cdot$, $\backslash$, $/$ and $\mathbf{1}$ (with $\to \mathbf{1}$ as an axiom); the additive rules for $\wedge$ and $\vee$; dereliction $\Gamma_1, A, \Gamma_2 \to C \,/\, \Gamma_1, {!}^s A, \Gamma_2 \to C$; promotion ${!}^{s_1}A_1, \dots, {!}^{s_n}A_n \to B \,/\, {!}^{s_1}A_1, \dots, {!}^{s_n}A_n \to {!}^s B$ when $s_j \succeq s$ for all $j$; and, for the labels that allow them,

$$
\frac{\Gamma_1, \Gamma_2 \to C}{\Gamma_1, {!}^s A, \Gamma_2 \to C}\ (s \in \mathcal{W}), \qquad \frac{\Gamma_1, {!}^s A, \Delta, {!}^s A, \Gamma_2 \to C}{\Gamma_1, {!}^s A, \Delta, \Gamma_2 \to C} \ \text{and} \ \frac{\Gamma_1, {!}^s A, \Delta, {!}^s A, \Gamma_2 \to C}{\Gamma_1, \Delta, {!}^s A, \Gamma_2 \to C}\ (s \in \mathcal{C}),
$$

$$
\frac{\Gamma_1, \Delta, {!}^s A, \Gamma_2 \to C}{\Gamma_1, {!}^s A, \Delta, \Gamma_2 \to C} \ \text{and} \ \frac{\Gamma_1, {!}^s A, \Delta, \Gamma_2 \to C}{\Gamma_1, \Delta, {!}^s A, \Gamma_2 \to C}\ (s \in \mathcal{E}).
$$

The contraction rules are *non-local*: the two copies of ${!}^s A$ need not be adjacent. $\mathrm{SMALC}_\Sigma$ denotes the calculus without cut; cut is admissible in it. Its fragment with only $\cdot$, $\backslash$, $/$ and the ${!}^s$ is $\mathrm{SLC}_\Sigma$, and adding $\mathbf{1}$ gives $\mathrm{SLC}^{\mathbf{1}}_\Sigma$; by the subformula property these are conservative fragments.

## Depends on

- [Derivability in the Lambek calculus](../../../TheoryOfComputation/np-completeness/strings-and-puzzles/lambek-calculus-derivability/derivable.md)

## Proof depends on

None.

## Expansion

Unlike the Lambek calculus of the linked page, antecedents may be empty here (no Lambek restriction), which the source notes is needed for compatibility with the modalities. Non-local contraction together with weakening yields exchange, which explains the condition $\mathcal{W} \cap \mathcal{C} \subseteq \mathcal{E}$. Cut elimination is Corollary 3 of the source, proved through an embedding into cyclic linear logic with subexponentials.

## Sources

- M. Kanovich, S. Kuznetsov, V. Nigam and A. Scedrov, "Subexponentials in non-commutative linear logic", *Mathematical Structures in Computer Science* 29(8):1217–1249, 2019, doi:10.1017/S0960129518000117; read as arXiv:1709.03607v1, <https://arxiv.org/abs/1709.03607v1>: Section 2 (signatures, formulas and rules of $\mathrm{SMALC}_\Sigma$ and its fragments) and Corollary 3 of arXiv:1709.03607v1 (cut elimination).
