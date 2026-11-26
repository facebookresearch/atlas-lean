# Cost of a ski-rental strategy

Renting skis costs $1$ per day and buying them costs a
natural number $B$. The cost $\mathrm{cost}_B(s, d) \in \mathbb{N}$ of a strategy $s$ for a season
of $d \in \mathbb{N}$ days is $(t - 1) + B$ if $s$ buys on a day $t$ with $1 \le t \le d$ (rent for
$t - 1$ days, then buy), and $d$ otherwise, that is, if $s$ rents forever or buys on a day $t$
with $t = 0$ or $t > d$ (rent every day).
