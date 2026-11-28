# Correctness of LL(1) parse table generation

There is a total function $\mathrm{parseTableOf}$ from context-free grammars to either an error or an LL(1) parse table, computing $\mathrm{NULLABLE}$, $\mathrm{FIRST}$ and $\mathrm{FOLLOW}$ by iteration to a fixed point, such that, in the sense of [correct parse tables](ll-1-lookahead-and-correct-parse-tables.md):

1. **Soundness.** If $\mathrm{parseTableOf}(G)$ returns a table, that table is correct for $G$.
2. **Completeness.** If $G$ has no two productions with the same left-hand side and right-hand side, whatever their actions, and $G$ has a correct table, then $\mathrm{parseTableOf}(G)$ returns a table with the same entries.

Table entries are productions together with their semantic actions.

**Proof idea.** Each analysis is shown sound by proving that soundness is an invariant of the iteration, and complete by proving that its fixed point is complete; the iterations terminate because each pass either reaches a fixed point or strictly enlarges a set bounded by the finitely many symbols.

## Depends on

- [LL(1) lookahead and correct parse tables](ll-1-lookahead-and-correct-parse-tables.md)

## Sources

- S. Lasser, C. Casinghino, K. Fisher and C. Roux, "A verified LL(1) parser generator", *10th International Conference on Interactive Theorem Proving (ITP 2019)*, LIPIcs 141, 2019, 24:1–24:18, <https://drops.dagstuhl.de/storage/00lipics/lipics-vol141-itp2019/LIPIcs.ITP.2019.24/LIPIcs.ITP.2019.24.pdf>, Section 3: the structure of the generator (3.1), the NULLABLE analysis, its termination, soundness and completeness (3.2–3.4, Theorems mkNullableSet_correct, mkNullableSet_sound and mkNullableSet_complete), and Section 3.5, Theorems parseTableOf_sound and parseTableOf_complete with the unique_productions hypothesis.
