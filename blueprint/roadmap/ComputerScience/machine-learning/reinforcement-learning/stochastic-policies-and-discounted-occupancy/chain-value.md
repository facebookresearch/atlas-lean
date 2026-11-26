# Discounted value of a Markov chain

For a row-stochastic matrix $P$ on a finite set of states, $0 \le \gamma < 1$ and a state reward $f$,
the discounted value of the chain $P$ with reward $f$: the unique solution $V$ of
$V = f + \gamma P V$, that is, the value of the one-action MDP with reward $f$ and transitions $P$.
