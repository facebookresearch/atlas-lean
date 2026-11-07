# Augmented $k$-Dyck paths

For natural numbers $k$ and $n$, write $U = (1,1)$ and
$D^{(k)} = (k,-k)$. A $k$-Dyck path of size $n$ is a word of length $(k+1)n$ in the letters $U$
and $D^{(k)}$ that has exactly $n$ letters $D^{(k)}$ and $k$ times as many letters $U$ as letters
$D^{(k)}$, and in which every prefix has at least $k$ times as many letters $U$ as letters
$D^{(k)}$. The augmented path of such a word is the word in the skew Dyck steps $U$, $D$, $L$
obtained by keeping each letter $U$ and replacing each letter $D^{(k)}$ by $U D^{k-1} L D$, where
$D^{k-1}$ means $k - 1$ copies of $D$ (none when $k \le 1$). The set $\hat{D}_n^{(k)}$ of
augmented $k$-Dyck paths of size $n$ is the set of the augmented paths of the $k$-Dyck paths of
size $n$.

The definition is used for $k \ge 2$.

## Sources

- Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Section 2.
