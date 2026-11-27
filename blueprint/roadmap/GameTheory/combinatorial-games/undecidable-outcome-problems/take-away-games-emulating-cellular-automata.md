# Take-away games emulating cellular automata

Larsson's impartial take-away games are played on a heap of matches and a heap of black and white tokens, with move sizes tied to the previous move; their outcomes reproduce the space-time diagram of a one-dimensional cellular automaton CA(A, γ, Γ), which for γ = 1, Γ = 0 is rule 110.

Fix integers $\gamma, \Gamma \ge 0$ and a doubly infinite binary string $A = (a_x)_{x \in \mathbb{Z}}$.

**The automaton $\mathrm{CA}(A, \gamma, \Gamma)$.** Put $a_x^0 = a_x$. For $y > 0$, let $a_x^y = 0$ if $a_{x-1}^{y-1} = a_x^{y-1} = 0$ or if $a_{x-\Gamma-1}^{y-1} = \cdots = a_{x+\gamma}^{y-1} = 1$, and $a_x^y = 1$ otherwise. (The source's display prints the second index of the first condition as $i$; the rule 60 case below fixes it as $x$.) For $\gamma = \Gamma = 0$ this is $a_x^y = a_{x-1}^{y-1} \oplus a_x^{y-1}$, Wolfram's rule 60. For $\gamma = 1$, $\Gamma = 0$ a cell becomes $0$ exactly when it and its left neighbor are $0$ or it and both neighbors are $1$; reading the tape from right to left, this is the [elementary cellular automaton](../../../TheoryOfComputation/equivalence-of-models/cellular-automata/elementary-cellular-automata-and-wolfram-numbers.md) rule 110.

**The games $\mathrm{G}(A, \gamma, \Gamma)$.** A position is a triple $(X, Y, m_p)$: a *tape-heap* of $X$ ordered tokens, a *time-heap* of $Y$ matches, and the number $m_p$ of matches the other player removed in the previous move. For a shift $\xi \in \mathbb{Z}$, the $i$-th token from the bottom is black if $a_{\xi+i} = 1$ and white otherwise ($1 \le i \le X$). A move has two parts:

1. remove $t$ tokens from the top of the tape-heap, where $\gamma(m-1) \le t \le \gamma m + m_p + \Gamma$; if fewer than $\gamma(m-1)$ tokens remain, all of them may be removed;
2. remove $m$ matches with $1 \le m \le Y$; after the removal in part 1, the whole time-heap ($m = Y$) may be removed only if none of the top $Y$ remaining tokens is black.

The new position is $(X - t, Y - m, m)$. Play is normal: a player who cannot move (no matches left) loses. These are [impartial games](../sprague-grundy-theorem/impartial-game.md): the moves depend only on the position, and every move removes at least one match. $\mathrm{G}(A, 1, 0)$ is the *rule 110 game*.

**Super-critical positions and periodic outcomes.** The tape-heap of $(X, Y, m_p)$ is *super-critical* if $X \ge (\Gamma + \gamma + 1) Y + m_p$. The family $\mathrm{G}(A, \gamma, \Gamma)$ has *two-dimensional eventually periodic outcomes* with period $(\delta', \rho')$ if, for every shift $\xi$ and every $m_p$, for all but finitely many $(X, Y)$, the positions $(X, Y, m_p)$ and $(X + \delta', Y + \rho', m_p)$, both with super-critical tape-heaps, are both [P-positions](../sprague-grundy-theorem/is-p.md) or both N-positions.

## Depends on

- [Impartial game](../sprague-grundy-theorem/impartial-game.md)
- [P-positions](../sprague-grundy-theorem/is-p.md)
- [Elementary cellular automata and Wolfram numbers](../../../TheoryOfComputation/equivalence-of-models/cellular-automata/elementary-cellular-automata-and-wolfram-numbers.md)

## Proof depends on

None.

## Expansion

The defining fact of the family is Theorem 2 of the source: for the game with shift $0$ and $x \ge (\Gamma + 1) y + m_p$, the position $(x + \gamma y, y, m_p)$ is a P-position exactly when $a_x^y = \cdots = a_x^{y + m_p - 1} = 0$ and, if $y > 0$, $a_x^{y-1} = 1$. So the P-positions of super-critical positions encode the space-time diagram of $\mathrm{CA}(A, \gamma, \Gamma)$, and by Lemma 3 of the source the automaton's updates are two-dimensional eventually periodic exactly when the game outcomes are.

## Sources

- U. Larsson, "Impartial games emulating one-dimensional cellular automata and undecidability", *Journal of Combinatorial Theory, Series A* 120(5):1116–1130, 2013, doi:10.1016/j.jcta.2013.02.009 (checked with Crossref); read as arXiv:1201.1039v1, <https://arxiv.org/abs/1201.1039v1>: Section 2 (game rules (I) and (II), the definition of CA(A, γ, Γ), Theorem 2, Lemma 3 and the definition of super-critical tape-heaps) and Section 4 (the rule 110 game).
