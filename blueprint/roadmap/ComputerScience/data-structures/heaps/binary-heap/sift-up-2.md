# Sift-up with comparison and swap counts

Given an array $a$ of length $|a|$ over a
linearly ordered type and an index $i$, this computes the sift-up of $a$ at $i$ together
with a cost $(c, s) \in \mathbb{N} \times \mathbb{N}$, where $c$ counts value comparisons
and $s$ counts swaps. If $i \ge |a|$ or $i = 0$, the result is $a$ with cost $(0, 0)$.
Otherwise let $p = \lfloor (i - 1)/2 \rfloor$ be the parent of $i$. If $a_i < a_p$, the
result is this sift-up at $p$ of the array obtained from $a$ by exchanging the entries at
positions $i$ and $p$, with cost $(1, 1)$ plus the cost of that recursive sift-up;
otherwise the result is $a$ with cost $(1, 0)$.
