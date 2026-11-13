# Z-values are longest common prefix lengths

Let $\alpha$ be a type with a lawful Boolean
equality test, let $s = s_0 \dots s_{n-1}$ be a word over $\alpha$, and let $Z$ be the Z-array
computed by the Z-algorithm on $s$. For every position $i < n$ and every natural number $q$,
$q \le Z_i$ holds if and only if $q \le n - i$ and $s_k = s_{i+k}$ for all $k < q$. Hence $Z_i$ is
the length of the longest common prefix of $s$ and its suffix $s_i \dots s_{n-1}$.
