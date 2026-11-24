# Hedge weights after a sequence of rounds

Let $\eta \in \mathbb{R}$ be a learning rate,
let $w \in \mathbb{R}^n$ be initial weights on $n$ experts, and let $\ell_1, \dots, \ell_T \in
\mathbb{R}^n$ be the loss vectors of $T$ rounds, given as a list. The weights after these rounds
are obtained from $w$ by applying the Hedge update once per round, in the order of the list:
round $t$ multiplies the weight of each expert $i$ by $e^{-\eta \ell_t(i)}$. For the empty list
of rounds the weights are $w$.
