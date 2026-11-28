# Sine-Presburger arithmetic is undecidable with four quantifier blocks

The set of true sentences of Presburger arithmetic extended by the sine function, with quantifiers over the integers, is undecidable already for prenex sentences with four alternating quantifier blocks of at most 3388 variables each.

**Setting (Blanchard and Hieronymi).** Let $\mathcal{L}_{\sin} = \{<, +, 0, 1, \sin, (\lambda_q)_{q \in \mathbb{Q}}\}$, where $\lambda_q(x) = qx$. A *sine-Presburger sentence* ($\sin$-PA sentence) is a first-order $\mathcal{L}_{\sin}$-sentence in prenex normal form, interpreted over the real numbers with all quantifiers ranging over $\mathbb{Z}$:

$$
Q_1 x_1 \in \mathbb{Z}^{n_1} \cdots Q_r x_r \in \mathbb{Z}^{n_r}\; \Phi(x_1, \dots, x_r),
$$

where the $Q_i \in \{\forall, \exists\}$ alternate and $\Phi$ is a Boolean combination of inequalities between terms built from the variables and rational numbers by addition, rational scalar multiplication and nested applications of $\sin$. A sentence is $\exists^K\forall^K\exists^K\forall^K$ if it has four alternating blocks, starting with $\exists$, each of at most $K$ variables.

**Theorem (Blanchard and Hieronymi).** The set of true $\exists^K \forall^K \exists^K \forall^K$ $\sin$-PA sentences, where $K = 3388$, is undecidable (Theorem A of arXiv:2204.00099v2).

Without sine the truth of such sentences is decidable, since [Presburger arithmetic admits quantifier elimination](../../quantifier-elimination-for-presburger-arithmetic.md). Under Schanuel's conjecture, the set of true existential $\sin$-PA sentences is decidable (Theorem B of the source), whereas the set of true existential $\log$-PA sentences, with the natural logarithm in place of sine, is undecidable by a direct reduction from Hilbert's tenth problem (Proposition 5.1 of the source). The theory of $(\mathbb{R}, <, +, \sin, \mathbb{Z})$ was known to be undecidable (Hieronymi and Tychonievich); Theorem A sharpens this to sentences quantifying only over the integers, with an explicit bound.

## Depends on

- [Complete theory of a first-order structure](../../../first-order-logic/theory-of-structure.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The proof gives an $\exists^{10}\forall^{14}$ $\sin$-PA formula $\mathrm{Member}(\mathbf{X}, s, t)$ with $\mathbf{X} \in \mathbb{N}^4$ such that every finite set $S \subseteq \mathbb{N}^2$ equals $\{(s,t) : \mathrm{Member}(\mathbf{X}, s, t)\}$ for some $\mathbf{X}$; the construction codes finite sets through best approximations of $\sin X$ from below by values $\sin Y$ with $Y \le d$, using that the values $\sin n$, $n \in \mathbb{N}$, are dense in $[-1,1]$, in place of the Ostrowski representations used for irrational scalar multiplication. A result implicit in Hieronymi, Nguyen and Pak then shows that any expansion of $(\mathbb{N}, <, +)$ by a $6$-ary predicate coding all finite subsets of $\mathbb{N}^2$ in this way has an undecidable set of true $\exists^{50}\forall^3$ sentences with at most $242$ occurrences of the predicate, because it interprets the weak monadic second-order theory of the grid $(\mathbb{N}^2, s_1, s_2)$, which is undecidable. Substituting $\mathrm{Member}$ gives the bound $K = 3388$. A complete expansion links pages for the undecidability of the weak monadic second-order theory of the grid and for the coding result of Hieronymi, Nguyen and Pak.

## Sources

- E. Blanchard and P. Hieronymi, "Decidability bounds for Presburger arithmetic extended by sine", *Annals of Pure and Applied Logic* 175(10), 2024, article 103487, doi:[10.1016/j.apal.2024.103487](https://doi.org/10.1016/j.apal.2024.103487); read as arXiv:2204.00099v2 ([arXiv](https://arxiv.org/abs/2204.00099v2)), whose numbering is used: Theorems A and B of the introduction, Section 3 with Fact 3.1, derived from Hieronymi, Nguyen and Pak, and Proposition 5.1 in the conclusion.
