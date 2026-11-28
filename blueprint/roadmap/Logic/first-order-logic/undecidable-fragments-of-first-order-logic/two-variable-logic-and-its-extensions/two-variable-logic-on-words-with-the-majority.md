# Two-variable logic on words with the majority quantifier is undecidable

Satisfiability of two-variable first-order logic over finite words with the linear order, extended by a majority quantifier ("at least half of all positions satisfy φ"), is undecidable.

**Logic.** $\mathrm{FO}^2[<]$ is first-order logic over finite words with the two variables $x$ and $y$, ranging over positions, the linear order $<$ on positions, equality and unary letter predicates. $\mathrm{FO}^2_{\mathrm{Maj}}[<]$ adds the *majority quantifier*: for a word $w$,

$$
w \models \mathrm{Maj}\,x.\,\varphi \iff \tfrac{|w|}{2} \leq |\{p : w, p \models \varphi[x/p]\}| ,
$$

where $\varphi$ may contain $y$ free. Satisfiability asks whether a sentence has a finite model word.

**Theorem (Bednarczyk and Michaliszyn).** The satisfiability problem for $\mathrm{FO}^2_{\mathrm{Maj}}[<]$ is undecidable (Theorem 6.3).

This sharpens Lange's undecidability result for full first-order logic with majority, by bounding the number of variables, and that of Lodaya and Sreejith for $\mathrm{FO}^2[<,\mathrm{succ}]$ with Presburger constraints, since neither successor nor general counting is used.

## Depends on

- [Two-variable logic and its counting extension](two-variable-logic-and-its-counting-extension.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [LTL with past-majority or most-frequent-letter operators is undecidable](../../../temporal-logic/extensions-of-ltl-with-counting-and-data/ltl-with-past-majority-or-most-frequent-letter.md)

## Expansion

The formulas used in the undecidability proof for $\mathrm{LTL}_{\mathbf{F}}[\mathbf{M}]$ have only *shadowy* models: words of even length whose even positions carry a letter $\mathit{white}$ and whose odd positions carry a letter $\mathit{shadow}$. Shadowy words are definable in $\mathrm{FO}^2_{\mathrm{Maj}}[<]$ (Lemma 6.1), and an $\mathrm{LTL}_{\mathbf{F}}[\mathbf{M}]$ formula has a shadowy model iff its translation into $\mathrm{FO}^2_{\mathrm{Maj}}[<]$, which extends the standard translation of $\mathrm{LTL}_{\mathbf{F}}$ into $\mathrm{FO}^2[<]$, has a model (Lemma 6.2). This transfers undecidability.

## Sources

- Bartosz Bednarczyk and Jakub Michaliszyn, "“Most of” leads to undecidability: Failure of adding frequencies to LTL", in *Foundations of Software Science and Computation Structures (FoSSaCS 2021)*, Lecture Notes in Computer Science 12650, Springer, 2021, pp. 82–101, doi:10.1007/978-3-030-71995-1_5; read as arXiv:2007.01233v4, <https://arxiv.org/abs/2007.01233v4>: Theorem 6.3, Lemmas 6.1 and 6.2 and Section 6 of arXiv:2007.01233v4.
