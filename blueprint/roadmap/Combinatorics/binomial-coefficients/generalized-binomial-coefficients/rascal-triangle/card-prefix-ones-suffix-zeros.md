# Binary words with a prefix of ones and a suffix of zeros

Let $n, k, \ell, u$ be natural
numbers with $\ell \le k$ and $k + u \le n$, and let $B_k(n)$ be the set of binary words $w$ of
length $n$ with exactly $k$ ones and at most one ascent (a position $i$ with $w_i < w_{i+1}$).
The number of words in $B_k(n)$ whose first $\ell$ letters are all $1$ and whose last $u$
letters are all $0$ equals the Rascal number $R_{n-u-\ell, k-\ell}$, where
$R_{a,b} = b(a-b) + 1$ for $0 \le b \le a$.

## Sources

- Amelia Gibbs and Brian K. Miceli, "Two Combinatorial Interpretations of Rascal Numbers", Lemma 3.
