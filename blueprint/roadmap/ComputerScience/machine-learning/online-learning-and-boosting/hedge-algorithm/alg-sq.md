# Summed second moments of the Hedge losses

Let $\eta$ be a learning rate,
$w \in \mathbb{R}^n$ initial weights on $n$ experts and $\ell_1, \dots, \ell_T \in \mathbb{R}^n$
the losses of $T$ rounds. Set $w_1 = w$ and $w_{t+1}(j) = w_t(j) e^{-\eta \ell_t(j)}$. The summed
second moment is $\sum_{t=1}^T \bigl(\sum_j w_t(j) \ell_t(j)^2\bigr) / \sum_j w_t(j)$, the sum over
the rounds of the weighted second moment of that round's losses; a round whose total weight is
$0$ contributes $0$.
