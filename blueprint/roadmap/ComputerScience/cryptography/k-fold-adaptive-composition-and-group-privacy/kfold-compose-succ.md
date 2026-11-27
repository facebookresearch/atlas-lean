# Unfolding one step of the k-fold composition

For every $n$, the [$(n+1)$-fold adaptive composition](kfold-compose.md) at a database $d$ draws a transcript $t$ from the $n$-fold composition at $d$, then draws $a \sim K_n(t, d)$, and returns $(t, a)$.
