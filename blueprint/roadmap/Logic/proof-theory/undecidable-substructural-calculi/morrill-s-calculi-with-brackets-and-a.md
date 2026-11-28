# Morrill's calculi with brackets and a subexponential

Morrill's categorial calculi extend the Lambek calculus with brackets, bracket modalities and a subexponential ${!}$ whose formulas sit in commutative stoups; a bracket-aware contraction rule lets a ${!}$-formula be copied into a bracketed island, modeling parasitic extraction in natural language.

**Formulas** are built from variables and the unit $\mathbf{1}$ with the divisions $\backslash$, $/$, the product $\cdot$, the additives $\wedge$, $\vee$, the bracket modalities $\langle\rangle$ and $[]^{-1}$, and the subexponential ${!}$.

**Sequents.** A *stoup* $\zeta$ is a finite multiset of formulas, a *tree term* is a formula or a bracketed expression $[\Xi]$, and a *meta-formula* $\Xi$ is an expression $\zeta; \Gamma$ with $\Gamma$ a finite, possibly empty, sequence of tree terms (an empty stoup is omitted). Sequents are $\Xi \Rightarrow A$ with $A$ a formula; $\Xi(\dots)$ denotes a meta-formula with a distinguished sub-meta-formula.

**Rules common to both calculi.** The axiom $A \Rightarrow A$; the Lambek rules for $\backslash$, $/$, $\cdot$ and $\mathbf{1}$, in which stoups of premises are united; the additive rules; the bracket rules: from $\Xi(\zeta; \Delta_1, A, \Delta_2) \Rightarrow B$ infer $\Xi(\zeta; \Delta_1, [[]^{-1}A], \Delta_2) \Rightarrow B$; from $[\Xi] \Rightarrow A$ infer $\Xi \Rightarrow []^{-1}A$; from $\Xi(\zeta; \Delta_1, [A], \Delta_2) \Rightarrow B$ infer $\Xi(\zeta; \Delta_1, \langle\rangle A, \Delta_2) \Rightarrow B$; from $\Xi \Rightarrow A$ infer $[\Xi] \Rightarrow \langle\rangle A$; and for ${!}$, the left rule from $\Xi(\zeta, A; \Gamma_1, \Gamma_2) \Rightarrow B$ infer $\Xi(\zeta; \Gamma_1, {!}A, \Gamma_2) \Rightarrow B$ and the permutation rule from $\Xi(\zeta; \Gamma_1, A, \Gamma_2) \Rightarrow B$ infer $\Xi(\zeta, A; \Gamma_1, \Gamma_2) \Rightarrow B$.

**The two calculi.** In ${!}^{2015}_{\mathbf b}\mathbf{MALC}^{*}\mathbf{b}(\mathrm{st})$ the remaining rules are: from $\zeta; \Lambda \Rightarrow B$ infer $\zeta; \Lambda \Rightarrow {!}B$ ($\Lambda$ the empty sequence), and contraction, for a nonempty stoup $\zeta_2$:

$$
\frac{\Xi(\zeta_1, \zeta_2; \Gamma_1, [\zeta_2; \Gamma_2], \Gamma_3) \Rightarrow B}{\Xi(\zeta_1, \zeta_2; \Gamma_1, \Gamma_2, \Gamma_3) \Rightarrow B} .
$$

In ${!}^{2018}_{\mathbf b}\mathbf{MALC}^{*}\mathbf{b}(\mathrm{st})$ they are: from ${!}A \Rightarrow B$ infer ${!}A \Rightarrow {!}B$, and contraction

$$
\frac{\Xi(\zeta, A; \Gamma_1, [A; \Gamma_2], \Gamma_3) \Rightarrow B}{\Xi(\zeta, A; \Gamma_1, [[\Gamma_2]], \Gamma_3) \Rightarrow B} .
$$

Neither calculus has a cut rule. Removing the additive connectives and their rules gives the fragments ${!}^{2015}_{\mathbf b}\mathbf{L}^{*}\mathbf{b}(\mathrm{st})$ and ${!}^{2018}_{\mathbf b}\mathbf{L}^{*}\mathbf{b}(\mathrm{st})$. The *derivability problem* asks whether a given sequent is derivable.

## Depends on

- [Derivability in the Lambek calculus](../../../TheoryOfComputation/np-completeness/strings-and-puzzles/lambek-calculus-derivability/derivable.md)

## Proof depends on

None.

## Expansion

Morrill's full systems have up to 45 connectives; since they have no cut rule, these fragments are conservative in them. Cut is not admissible in the original systems, and the source also studies modified versions with cut elimination. In the 2018 calculus contraction instantiates a parasitic copy of a stoup formula inside a double-bracketed (strong) island, which then becomes single-bracketed, so that islands are not reused.

## Sources

- M. Kanovich, S. Kuznetsov and A. Scedrov, "The multiplicative-additive Lambek calculus with subexponential and bracket modalities", *Journal of Logic, Language and Information* 30:31–88, 2021, doi:10.1007/s10849-020-09320-9; read as arXiv:2008.00075v2, <https://arxiv.org/abs/2008.00075v2>: Section 3 ("Morrill's calculi with brackets and subexponential") of arXiv:2008.00075v2.
