# Zero external regret does not bound swap regret: an unbounded ratio with three actions

Already with $N = 3$ actions the ratio between swap regret and external regret is unbounded: for every real $M$ there are a horizon $T$, plays and losses on three actions with external regret strictly positive and swap regret divided by external regret greater than $M$ (Blum and Mansour, Exercise 4.2, "Show an example (even with $N = 3$) where the ratio between the external and swap regret is unbounded"). Thus no bound on swap regret in terms of external regret holds, in contrast with the reverse inequality external regret $\le$ swap regret.

## Proof sketch

Derived (not stated in the cited source, which poses the claim as an exercise): with deterministic play and binary losses, for every $m \in \mathbb{N}$ there are plays and losses over $T = 6m$ rounds with external regret $0$ and swap regret $3m$. Use a periodic construction with period $6$ on three actions in which every fixed action has the same total loss as the learner, so external regret vanishes, while a non-constant swap (sending each played action to the action that has loss $0$ in the rounds where it is played) saves a constant amount per period. Appending one round in which the learner loses and some fixed action does not makes the external regret equal to $1$ while the swap regret keeps growing with $m$.

## Depends on

- [Regret against a family of modification rules; internal regret](modification-rule-regret-and-internal-regret.md)
- [External regret is at most swap regret](../../../../GameTheory/not-yet-classified/part-02/regret/external-regret-le-swap-regret.md)

## Sources

- Avrim Blum and Yishay Mansour, "Learning, Regret Minimization, and Equilibria", in N. Nisan, T. Roughgarden, É. Tardos and V. V. Vazirani (eds.), Algorithmic Game Theory, Cambridge University Press, 2007, Chapter 4, Exercise 4.2.
