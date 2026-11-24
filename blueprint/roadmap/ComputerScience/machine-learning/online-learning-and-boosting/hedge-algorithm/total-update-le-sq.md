# A round costs weight in proportion to the algorithm's loss, up to a second-order term

Let $n > 0$, let $w$ be positive weights on $n$ experts, let $\ell$ be nonnegative losses, and let
$\eta \ge 0$. Let $w'$ be the Hedge update of $w$ with learning rate $\eta$, so that
$w'_i = w_i e^{-\eta \ell_i}$, and let $W$ and $W'$ be the total weights of $w$ and $w'$. Then
$W' \le W \exp(-\eta L + \eta^2 Q)$, where $L$ is the round's loss and $Q$ its weighted second
moment under the weights $w$.
