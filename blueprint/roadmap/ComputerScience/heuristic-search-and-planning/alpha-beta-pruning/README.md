# Alpha–beta pruning

- [Game tree](game-tree.md)
- [Number of leaves](leaves.md)
- [Number of leaves of a list of game trees](leaves-list.md)
- [Alpha-beta pruning](alpha-beta.md)
- [Alpha-beta scan of the children](alpha-beta-list.md)

## Scan bounds and order facts

- [Lower bound for the maximizer's scan](le-alpha-beta-list-true.md)
- [The minimizer's alpha-beta scan stays at or below its upper bound](alpha-beta-list-false-le.md)

## Cost

- [Alpha-beta never evaluates more leaves than the tree has](alpha-beta-time-le.md)
- [Cost of the alpha-beta scan](alpha-beta-list-time-le.md)

## The minimax value; from here on the order is bounded

- [Minimax value](minimax.md)
- [Minimax value of a list of positions](minimax-list.md)

## Correctness

- [Alpha-beta is correct](alpha-beta-spec.md)
- [Correctness of the alpha-beta scan](alpha-beta-list-spec.md)
- [Alpha-beta fails low when the minimax value is at most the lower bound](alpha-beta-le-of-minimax-le.md)
- [Alpha-beta is exact inside the window](alpha-beta-eq-of-mem-window.md)
- [Alpha-beta at or above the top of the window](le-alpha-beta-of-le-minimax.md)
- [Alpha-beta with the full window returns the minimax value](alpha-beta-bot-top.md)
