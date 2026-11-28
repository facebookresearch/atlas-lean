# Q-factor of a split with no bidirected edge across it

Let $b$ be a Bayesian network on $n$ nodes with values in a finite nonempty set and $L$ a set of latent nodes, and for a set $S$ of observed nodes let $Q[S](v)$ be the Q-factor of $S$ at the observed values $v$. If $T \subseteq H$ are sets of observed nodes and no bidirected edge of the latent projection joins a node of $T$ to a node of $H \setminus T$, then

$$Q[H](v) = Q[T](v)\, Q[H \setminus T](v)$$

(J. Tian and J. Pearl, On the testable implications of causal models with hidden variables, UAI 2002, Lemma 2, equation (20); Lemma 4(i) of their technical report R-290-L).
