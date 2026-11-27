# Subgame-perfect trigger strategies in the repeated prisoner’s dilemma

In the infinitely repeated prisoner's dilemma with stage payoffs $\pi(C,C) = 1$, $\pi(D,D) = 0$, $\pi(D,C) = 2$, $\pi(C,D) = -1$ and normalized discounted payoff $(1 - \delta) \sum_t \delta^t u_t$ with $0 \le \delta < 1$, a strategy profile is a subgame-perfect equilibrium iff no player gains from a one-shot deviation at any history. Grim trigger played by both players is subgame perfect iff $\delta \ge 1/2$, tit-for-tat played by both is subgame perfect iff $\delta = 1/2$ exactly, and the naive variant of grim trigger that plays $C$ unless the opponent has defected (ignoring its own defections) is not subgame perfect for any $\delta$: after its own defection it keeps playing $C$ against an opponent who now plays $D$ forever.

## Proof sketch

Discounting makes continuation payoffs continuous at infinity, so the one-shot deviation principle holds. For grim trigger compare $1$ with $(1 - \delta)\cdot 2$. For tit-for-tat the deviation incentive after $(C,C)$ requires $\delta \ge 1/2$ and forgiving after $(D,C)$ requires $\delta \le 1/2$.

## Depends on

- [Subgame-perfect equilibrium of a perfect-information game](../../noncooperative-games/von-neumann-s-minimax-theorem/extensive-form-and-sequence-form/perfect-information-refinements/subgame-perfect-equilibrium-of-a-perfect-information-game.md)
- [The one-shot incentive inequalities of grim trigger, in closed form](../../not-yet-classified/part-02/repeated-prisoners-dilemma/one-shot-incentives-iff.md)

## Proof depends on

- [One-shot deviation principle for finite perfect-information games](../../noncooperative-games/von-neumann-s-minimax-theorem/extensive-form-and-sequence-form/perfect-information-refinements/one-shot-deviation-principle-for-finite-perfect-information-games.md)

## Sources

- Eric Friedman, Paul Resnick and Rahul Sami, "Manipulation-Resistant Reputation Systems", Algorithmic Game Theory, Cambridge University Press, 2007.
- Eric J. Friedman and Paul Resnick, "The Social Cost of Cheap Pseudonyms", Journal of Economics & Management Strategy, 2001.
