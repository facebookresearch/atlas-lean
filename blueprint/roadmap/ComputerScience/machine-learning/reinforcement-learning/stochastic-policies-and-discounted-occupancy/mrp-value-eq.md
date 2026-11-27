# The value of a Markov reward process solves its Bellman equation

Let $P$ be a row-stochastic matrix on a finite set $S$ (nonnegative entries, each row summing to $1$) and let $0 \le \gamma < 1$. For every reward $c$ and state $s$, $V_c(s) = c(s) + \gamma \sum_{s'} P(s,s') V_c(s')$.
