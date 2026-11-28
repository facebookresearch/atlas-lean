# Eventual periodicity of the outcomes of the rule 110 game is undecidable

No algorithm decides, given nonempty finite binary strings L and R, a finite binary string C and a period, whether the outcomes of Larsson's impartial rule 110 game, with tokens colored by the string ...LLLCRRR..., are two-dimensionally eventually periodic with that period.

For nonempty finite binary strings $L$ and $R$ and a finite binary string $C$, which may be empty, write $\underline{L}\,C\,\underline{R}$ for the doubly infinite binary string that repeats $L$ to the left of $C$ and $R$ to the right of it. Its origin may be fixed arbitrarily, since the outcome condition quantifies over all shifts.

**Theorem (Larsson).** The following problem is undecidable. Input: nonempty finite binary strings $L$ and $R$, a finite binary string $C$ and a pair of integers $(\delta', \rho')$. Question: do the [rule 110 games](take-away-games-emulating-cellular-automata.md) $\mathrm{G}(\underline{L}\,C\,\underline{R}, 1, 0)$ have two-dimensional eventually periodic outcomes with period $(\delta', \rho')$?

This is Corollary 3 of the source; its proof transfers the corresponding undecidability for the updates of the rule 110 automaton from the initial string $\underline{L}\,C\,\underline{R}$ (Corollary 2, credited to Cook). The source also states (Corollary 4) that it is undecidable whether a certain finite path of alternating moves, which traverses Cook's F-glider, is optimal for both players in the rule 110 games with $\underline{L}\,C\,\underline{R}$ ending conditions; it omits the technical details of that proof. In its conclusion the source also states (Corollary 5) that it is undecidable whether the P-positions of Larsson's triangle placing game $\mathrm{T}(\underline{L}\,C\,\underline{R}, 1, 0)$ ultimately become two-dimensionally periodic. Whether convergence of two rule 110 game families is decidable is left open in the source.

## Depends on

- [Take-away games emulating cellular automata](take-away-games-emulating-cellular-automata.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Rule 110 is computationally universal](../../../TheoryOfComputation/equivalence-of-models/cellular-automata/rule-110-is-computationally-universal.md)

## Expansion

By Theorem 2 of the source, for super-critical tape-heaps with at least one match and $m_p \ge 1$ the P-positions of $\mathrm{G}(A, 1, 0)$ are read off the space-time diagram of $\mathrm{CA}(A, 1, 0)$ (the cases with no matches or with $m_p = 0$ are treated on the [definition page](take-away-games-emulating-cellular-automata.md)), and by Lemma 3 the game outcomes are two-dimensional eventually periodic with some period exactly when the automaton's updates are, with $\delta' = \delta + \gamma \rho$ and $\rho' = \rho$ translating the periods. Cook's emulation of cyclic tag systems by rule 110 makes eventual periodicity of the updates from $\underline{L}\,C\,\underline{R}$ undecidable, so the game question is undecidable too. A good expansion has pages for Theorem 2 (outcomes of $\mathrm{G}(A, \gamma, \Gamma)$ equal the automaton's pattern on super-critical tape-heaps, for $y \ge 1$ and $m_p \ge 1$) and Lemma 3 (equivalence of the two periodicity notions, both quantified over all large coordinates), and states Cook's periodicity consequence, Corollary 2 of the source, for a given period.

## Sources

- U. Larsson, "Impartial games emulating one-dimensional cellular automata and undecidability", *Journal of Combinatorial Theory, Series A* 120(5):1116–1130, 2013, doi:10.1016/j.jcta.2013.02.009 (checked with Crossref); read as arXiv:1201.1039v1, <https://arxiv.org/abs/1201.1039v1>: Corollaries 2–4 in Section 4 and Corollary 5 in Section 5 ("Conclusion"), Theorem 2 and Lemma 3 in Section 2; the triangle placing game is introduced in Section 3.
- M. Cook, "Universality in elementary cellular automata", *Complex Systems* 15(1):1–40, 2004, cited by the source for rule 110 (not read here).
