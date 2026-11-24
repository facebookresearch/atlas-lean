# Hedge weight update

For a learning rate $\eta \in \mathbb{R}$, weights $w \in \mathbb{R}^n$ on $n$ experts and losses $\ell \in \mathbb{R}^n$ of a round, the Hedge update multiplies each expert's weight by $e^{-\eta \ell_i}$: the new weights are $w'_i = w_i e^{-\eta \ell_i}$.
