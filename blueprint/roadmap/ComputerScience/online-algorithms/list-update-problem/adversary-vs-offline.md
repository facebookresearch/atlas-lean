# Online and offline costs on the adversary's sequence

Let $M$ be a nonempty list of $\ell$
distinct items, let $A$ be a deterministic online list-update algorithm on the items of $M$, let
$d$ be an item and $n$ a natural number, and let $\sigma$ be the adversary's sequence of $n$
requests against $A$ from its initial state, with default item $d$. Then the cost of $A$ on
$\sigma$ from its initial state is $n \ell$, and there are lists $L_0, L_1, L_2, \dots$, each a
rearrangement of $M$, with $L_0 = M$ such that the offline cost $C$ of this sequence of lists on
$\sigma$ satisfies $2 C \le n (\ell + 1) + 2 (\ell + \ell^2)$.
