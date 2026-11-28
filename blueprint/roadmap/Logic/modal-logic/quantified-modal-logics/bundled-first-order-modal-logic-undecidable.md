# The ∃◇ bundled fragment of first-order modal logic is undecidable over constant domains

Satisfiability over constant-domain Kripke models is undecidable for first-order modal formulas in which every quantifier is bundled with a modality as $\exists x \Diamond$ (dually $\forall x \Box$), even with only unary predicates.

**Bundled fragment.** Over countably many variables and predicate symbols, without equality, constants or function symbols, the *bundled fragment* $\mathrm{BFOML}$ of first-order modal logic has formulas

$$
\varphi ::= P\bar{x} \mid \neg\varphi \mid (\varphi \wedge \varphi) \mid \exists x \Box \varphi \mid \exists x \Diamond \varphi ,
$$

and $\mathrm{BFOML}^{\exists\Diamond}$ uses only the bundle $\exists x \Diamond$ (whose dual is $\forall x \Box$). A model $(W, D, \delta, R, \rho)$ is a [Kripke frame](../kripke-semantics/kripke-model.md) with a non-empty set $W$ of worlds and a non-empty domain $D$, with non-empty local domains $\delta(w) \subseteq D$, increasing along $R$, and interpretations of the predicates at each world; it has *constant domain* if $\delta(w) = D$ for all $w$. $M, w, \sigma \models \exists x \Diamond \varphi$ iff some $d \in \delta(w)$ and some $v$ with $wRv$ have $M, v, \sigma[x \mapsto d] \models \varphi$, and $M, w, \sigma \models \exists x \Box \varphi$ iff some $d \in \delta(w)$ has $M, v, \sigma[x \mapsto d] \models \varphi$ for all $v$ with $wRv$. Compare the full [quantified modal logics](quantified-modal-logic-ql.md).

**Theorem (Padmanabha, Ramanujam and Wang).** The satisfiability problem for $\mathrm{BFOML}^{\exists\Diamond}$ sentences over constant domain models is undecidable, even when all predicates are unary (Section 3 of the source, via Theorem 3.1: a sentence of first-order logic over one binary predicate without equality is satisfiable iff its translation is constant-domain satisfiable).

By contrast, the source shows that $\mathrm{BFOML}^{\exists\Box}$ is decidable over constant domain models and that the whole bundled fragment is decidable over increasing domain models, in both cases with PSPACE-complete satisfiability (Corollaries 4.6 and 4.3).

## Depends on

- [Kripke model](../kripke-semantics/kripke-model.md)
- [Quantified modal logic QL](quantified-modal-logic-ql.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Validity of first-order sentences is undecidable](../../../TheoryOfComputation/undecidable-problems/validity-of-first-order-sentences-is-undecidable.md)

## Expansion

The proof reduces satisfiability of first-order sentences over a single binary predicate $R$, without equality, which is undecidable. An atom $R(x, y)$ is translated as $\exists z \Diamond (p(x) \wedge q(y))$ with fresh $z$ and two unary predicates $p, q$; the translation of a prenex sentence $\alpha$ is conjoined with sentences that use the $\forall \Box$ bundle and the constant domain to make all worlds at the relevant modal depth interpret $R$ in the same way, and $\alpha$ is satisfiable iff its translation is constant-domain satisfiable. A complete expansion links the undecidability of first-order satisfiability over one binary relation symbol without equality, which [Validity of first-order sentences is undecidable](../../../TheoryOfComputation/undecidable-problems/validity-of-first-order-sentences-is-undecidable.md) states only for the language of arithmetic.

## Sources

- Anantha Padmanabha, R. Ramanujam and Yanjing Wang, "Bundled fragments of first-order modal logic: (un)decidability", in *38th IARCS Annual Conference on Foundations of Software Technology and Theoretical Computer Science (FSTTCS 2018)*, LIPIcs 122, 43:1–43:20, 2018, doi:[10.4230/LIPIcs.FSTTCS.2018.43](https://doi.org/10.4230/LIPIcs.FSTTCS.2018.43). Numbering of the version read, arXiv:1803.10508v1: Definitions 2.1 and 2.2, Theorem 3.1 in Section 3, and Corollaries 4.3 and 4.6.
