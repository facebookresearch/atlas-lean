# Loss of the Hedge algorithm

Let $\eta$ be a learning rate, $w \in \mathbb{R}^n$ initial
weights on $n$ experts and $\ell_1, \dots, \ell_T \in \mathbb{R}^n$ the losses of $T$ rounds. Set
$w_1 = w$ and $w_{t+1}(j) = w_t(j) e^{-\eta \ell_t(j)}$. The algorithm's total loss is
$\sum_{t=1}^T \bigl(\sum_j w_t(j) \ell_t(j)\bigr) / \sum_j w_t(j)$, the sum over the rounds of
the weighted average of that round's losses; a round whose total weight is $0$ contributes
$0$.
