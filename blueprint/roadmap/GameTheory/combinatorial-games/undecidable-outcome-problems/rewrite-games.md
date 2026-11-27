# Rewrite games

A rewrite game is played on words: a finite set of rewriting rules u → v is fixed, a move replaces one occurrence of a left-hand side u in the current word by v, and the player who cannot move loses. It is strongly terminating when every rule shortens the word.

Let $A$ be a finite alphabet and $R \subseteq A^* \times A^*$ a finite set of [rewriting rules](../../../TheoryOfComputation/undecidable-problems/string-rewriting-systems/rule.md) $u \to v$. A rule applies to a word $w = xuy$ with $x, y \in A^*$ and yields $xvy$. The system is *terminating* if no infinite chain of rule applications starts from any word.

**The game.** The *rewrite game* of a terminating system $R$ has the words of $A^*$ as positions; from a position $w$ the moves lead to the words obtained from $w$ by one rule application. Two players alternate moves from a starting word; a player facing a word to which no rule applies (a *final position*) cannot move and loses (normal play). Rewrite games are impartial. A position is an N-position if the player to move has a winning strategy and a [P-position](../sprague-grundy-theorem/is-p.md) otherwise.

**Strong termination.** The game is *strongly terminating* if $|u| > |v|$ for every rule $u \to v$ of $R$. Then every position has finitely many moves and the length of the word strictly decreases along moves, so the game from any starting word is an [impartial game](../sprague-grundy-theorem/impartial-game.md) with rank the word length. Octal games, and the taking-and-merging games over $\{a, b\}$, whose rules all have the form $a^k \to \varepsilon$ or $b^k \to \varepsilon$ (removing a block can merge the blocks on either side), are rewrite games.

## Depends on

- [Rewriting rules](../../../TheoryOfComputation/undecidable-problems/string-rewriting-systems/rule.md)
- [Impartial game](../sprague-grundy-theorem/impartial-game.md)
- [P-positions](../sprague-grundy-theorem/is-p.md)

## Proof depends on

None.

## Expansion

Rewrite games were introduced by Waldmann; the source fixes the conventions above (Section 1) and the notion of strong termination (Definition 22).

## Sources

- E. Duchêne, V. Marsault, A. Parreau and M. Rigo, "Taking-and-merging games as rewrite games", *Discrete Mathematics & Theoretical Computer Science* 22(4), 2020, doi:10.23638/DMTCS-22-4-5 (checked with Crossref); read as arXiv:1902.07011v4, <https://arxiv.org/abs/1902.07011v4>: Section 1 (definition of rewrite games) and Definition 22.
- J. Waldmann, "Rewrite games", in *Rewriting Techniques and Applications (RTA 2002)*, LNCS 2378, pp. 144–158, Springer, 2002, cited by the source for the definition (not read here).
