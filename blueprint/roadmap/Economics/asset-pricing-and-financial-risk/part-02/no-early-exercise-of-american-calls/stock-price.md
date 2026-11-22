# Stock price at a node of the binomial tree

For real `S₀`, `u`, `d`, the stock price at the node of the binomial tree reached by a finite
history `s` of up and down moves, with initial price `S₀`, up factor `u` and down factor `d`, is
`S₀ u^(number of up moves) d^(number of down moves)`.

This is the same function as
[Stock price at a node of the binomial tree](../replication-in-the-multi-period-binomial-model/price.md).
Here it is given in closed form; the linked page defines it by recursion on the history.
