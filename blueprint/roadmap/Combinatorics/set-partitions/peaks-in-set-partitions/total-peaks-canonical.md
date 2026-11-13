# Total number of peaks over set partitions

For natural numbers $n$ and $k$, call a word
$\pi = \pi_1 \cdots \pi_n$ on the alphabet $\{0, \dots, k-1\}$ a restricted growth word if it uses
every letter and, for every position $i$, every letter smaller than $\pi_i$ occurs among
$\pi_1, \dots, \pi_{i-1}$; these words encode the partitions of $[n]$ into $k$ blocks. A peak of
$\pi$ is a position $i$ with $1 < i < n$ and $\pi_{i-1} < \pi_i > \pi_{i+1}$. Then the total
number of peaks, summed over all restricted growth words of length $n$ on $k$ letters, equals

$$\binom{k}{2} S(n-1, k) + \sum_{j=2}^{k} \left(j \binom{j}{2} - \binom{j+1}{3}\right)
\sum_{i=3}^{n-k} j^{i-3}\, S(n-i, k),$$

where $S(m, k)$ is the Stirling number of the second kind, $n - 1$ is read as $0$ when $n = 0$,
and the inner sum is empty when $n - k < 3$.

## Sources

- Toufik Mansour and Mark Shattuck, "Counting Peaks and Valleys in a Partition of a Set", Journal of Integer Sequences 13 (2010), Article 10.6.8, Corollary 2, lines 388-394, <https://cs.uwaterloo.ca/journals/JIS/VOL13/Shattuck/shattuck3.tex>.
