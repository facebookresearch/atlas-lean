# Prefix probabilities of the Fisher–Yates shuffle

Let $k \le n$ and let
$a_0, \dots, a_{k-1}$ be distinct elements of $\{0, \dots, n - 1\}$. Run the Fisher–Yates
computation on the vector $(0, 1, \dots, n - 1)$ with every draw history $d$, which assigns to each
position $i < n$ a number $d_i$ with $0 \le d_i < n - i$, and give each history weight $1/n!$.
Then the total weight of the histories whose output vector has entry $a_p$ at position $p$ for
every $p < k$ equals $(n - k)!/n!$.

There are exactly $n!$ draw histories, so this is the probability of the prefix under a uniformly
random history. The cases $k = 0$ and $k = n$ are included.
