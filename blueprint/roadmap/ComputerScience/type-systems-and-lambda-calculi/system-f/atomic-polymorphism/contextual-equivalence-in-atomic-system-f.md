# Contextual equivalence in atomic System F is undecidable

In atomic System F, the predicative fragment of System F where a universal type may be instantiated only by a type variable, contextual equivalence of closed terms with Church numerals as observations is undecidable, although typability and type checking are decidable.

**Atomic System F.** Types are $A ::= X \mid A \to B \mid \forall X.\, A$. System $\mathrm{F}_{\mathrm{at}}$ is the fragment of System F whose typing rules are those of System F except that $\forall$-elimination may instantiate $\forall X.\, A$ only with a type variable, giving $A[Y/X]$. Write $\mathsf{Nat} = \forall X.\,(X \to X) \to (X \to X)$ and $\mathsf{Bool} = \forall X.\, X \to X \to X$. For closed terms $t, u$ of type $A$ in $\mathrm{F}_{\mathrm{at}}$, $t \simeq_{\mathsf{Nat}} u$ holds if $\mathcal{C}[t] \simeq_{\beta\eta} \mathcal{C}[u]$ for every context $\mathcal{C}[\,]$ of $\mathrm{F}_{\mathrm{at}}$ that turns a term of type $A$ into a closed term of type $\mathsf{Nat}$; $\simeq_{\mathsf{Bool}}$ is defined in the same way with $\mathsf{Bool}$ as the type of observations.

**Theorem (Pistone and Tranchini).** The congruences $\simeq_{\mathsf{Nat}}$ and $\simeq_{\mathsf{Bool}}$ of $\mathrm{F}_{\mathrm{at}}$ are both undecidable: no algorithm decides, given a type $A$ and closed terms $t, u$ of type $A$ in $\mathrm{F}_{\mathrm{at}}$, whether $t \simeq_{\mathsf{Nat}} u$, and none decides whether $t \simeq_{\mathsf{Bool}} u$.

In System F the two congruences coincide, but in $\mathrm{F}_{\mathrm{at}}$ they must be treated separately because the equality test on numerals is not typable there. Restricted to terms of type $\mathsf{Nat} \to \dots \to \mathsf{Nat}$ representing numerical functions, $\simeq_{\mathsf{Nat}}$ is decidable in $\mathrm{F}_{\mathrm{at}}$, while the authors show it undecidable for ML-polymorphism and for System $\mathrm{F}_1$.

## Depends on

- [Scoped types of pure System F](../scoped-pure-system-f/ty.md)
- [Extrinsic typing of pure System F terms](../the-five-typing-rules-of-pure-system-f/typing.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The proof reduces the type inhabitation problem of a suitable extension of $\mathrm{F}_{\mathrm{at}}$ to contextual equivalence: from a type $A$ it builds two terms $u_A$, $v_A$ that are contextually equivalent exactly when $A$ is not inhabited. Type inhabitation in $\mathrm{F}_{\mathrm{at}}$ is undecidable (Corollary 3.1 of the source). The source derives this from Proposition 3.1, a translation of the $\to,\forall$-fragment of dyadic intuitionistic first-order logic into $\mathrm{F}_{\mathrm{at}}$ that preserves provability, and Theorem 3.2 (Theorem 11.6.14 of Sørensen and Urzyczyn's *Lectures on the Curry–Howard Isomorphism*), which reflects inhabitation in System F back to provability; since $\mathrm{F}_{\mathrm{at}}$ is a fragment of System F, the reflection applies to it. Remark 3.2 of the source notes that the undecidability of the atomic fragment of second-order intuitionistic logic does not give this result, because disjunction is not faithfully definable in $\mathrm{F}_{\mathrm{at}}$. A good expansion adds pages for the undecidability of provability in the $\to,\forall$-fragment of dyadic intuitionistic first-order logic and for its embedding into $\mathrm{F}_{\mathrm{at}}$ (Proposition 3.1 and Theorem 3.2), adapting the System F argument behind [inhabitation in System F](../curry-style-system-f/inhabitation-in-system-f-is-undecidable.md).

## Sources

- Paolo Pistone and Luca Tranchini, "What's Decidable About (Atomic) Polymorphism?", 6th International Conference on Formal Structures for Computation and Deduction (FSCD 2021), Leibniz International Proceedings in Informatics 195, Article 27, 2021, <https://doi.org/10.4230/LIPIcs.FSCD.2021.27>; the contributions in the introduction, Corollary 3.1 (type inhabitation) in Section 3, Theorem 4.2 and Corollary 4.1 (type checking and typability) in Section 4, Definition 5.1 (contextual equivalence) and Proposition 5.6 (numerical functions) in Section 5, and Theorem 6.4 in Section 6, "Contextual Equivalence is Undecidable" of arXiv:2105.00748v1 (the copy read), <https://arxiv.org/abs/2105.00748v1>.
