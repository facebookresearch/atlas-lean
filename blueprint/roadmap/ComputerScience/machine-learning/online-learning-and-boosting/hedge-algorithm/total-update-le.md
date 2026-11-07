# A round costs weight in proportion to the algorithm's loss

Let $n > 0$, let $w$ be
positive weights on $n$ experts, let $\ell$ be losses with $0 \le \ell_i \le 1$ for every $i$, and
let $\eta$ be a real number. Let $w'$ be the Hedge update of $w$ with learning rate $\eta$, so that
$w'_i = w_i e^{-\eta \ell_i}$, and let $W$ and $W'$ be the total weights of $w$ and $w'$. Then
$W' \le W \exp(-(1 - e^{-\eta}) L)$, where $L$ is the round's loss under the weights $w$.
