# Winning positions of rewrite games in a regular language are undecidable

No algorithm decides, given a strongly terminating rewrite game and a regular language of starting positions, whether the language contains a position that is a win for the player to move, even when the language is star-free.

**Theorem (Duchêne, Marsault, Parreau and Rigo).** The following problem is undecidable. Input: a [strongly terminating rewrite game](rewrite-games.md) $G$, given by its finite alphabet and finite rule set, and a regular language $L$ of starting positions, given by a finite automaton. Question: does $L$ contain an N-position of $G$, that is, a word that is not a [P-position](../sprague-grundy-theorem/is-p.md)? The problem stays undecidable when $L$ is restricted to [star-free](../../../TheoryOfComputation/not-yet-classified/part-05/part-02/varieties/is-star-free.md) languages.

For a single strongly terminating game and a single word the outcome is computable, by exhaustive search of the finite game tree; the undecidability comes from the infinite language of starting positions. The source conjectures that it is also undecidable whether the set of winning positions of a strongly terminating game is a regular language.

## Depends on

- [Rewrite games](rewrite-games.md)
- [P-positions](../sprague-grundy-theorem/is-p.md)
- [Star-free languages](../../../TheoryOfComputation/not-yet-classified/part-05/part-02/varieties/is-star-free.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Halting is undecidable](../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

The reduction is from the halting problem of a deterministic Turing machine $T$ on the empty word. The game's alphabet consists of the states and tape symbols of $T$, an erasable padding symbol $\#$ and four head symbols that record the head's direction and the player to move. Its rules simulate one transition of $T$ while erasing padding symbols, which makes the game strongly terminating, and a halting rule fires when $T$ enters a halting state. The language of starting positions is $L = \natural\, {\lhd_A}\, q_0\, (\# + \beta)^*$, where $\natural$ is the left end marker of the tape (a dollar sign in the source) and $\beta$ the blank: the initial configuration followed by any mix of padding and blanks, which is star-free. From such a position every move is forced, so the game is a zero-player game that runs $T$ for as long as the padding lasts (Proposition 27). If a position of $L$ is a win for the first player, then $T$ halts (Corollary 30); conversely, if $T$ halts on the empty word, enough padding gives a winning position in $L$ (Corollary 33). A good expansion has a page for the halting problem of a deterministic Turing machine on the empty word and pages for the construction and for Corollaries 30 and 33.

## Sources

- E. Duchêne, V. Marsault, A. Parreau and M. Rigo, "Taking-and-merging games as rewrite games", *Discrete Mathematics & Theoretical Computer Science* 22(4), 2020, doi:10.23638/DMTCS-22-4-5 (checked with Crossref); read as arXiv:1902.07011v4, <https://arxiv.org/abs/1902.07011v4>: Problem 23 and Theorem 24 in Section 5, the construction in Section 5.1, Proposition 27 in Section 5.2, Corollary 30 in Section 5.3, Corollary 33 in Section 5.4, and the conjecture closing Section 5.
