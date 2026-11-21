# Outcome of the metered parking scheme

Let $t, n \in \mathbb{N}$, number the $n$ spots
$0, \dots, n-1$, and let $a_0, a_1, \dots, a_{m-1}$ be a list of preferences in $\mathbb{N}$.
Cars arrive in order, and car $i$ parks in the least spot $s$ with $a_i \le s < n$ that is not
taken by one of the previous $t$ cars (cars $\max(0, i - t), \dots, i - 1$) that parked; if
there is no such spot, car $i$ fails. The outcome is the list whose $i$-th entry is the spot of
car $i$, or a failure marker if car $i$ fails. Thus after car $j$ arrives, car $j - t$ leaves,
and only the cars among the last $t$ entries of the outcome so far occupy spots.

## Sources

- Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking Functions*, INTEGERS 25 (2025), Article A73, Section 1 (definition of the `t`-metered scheme) and Section 2 (definition of the outcome).
