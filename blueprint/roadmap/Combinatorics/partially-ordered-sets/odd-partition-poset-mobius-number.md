# Stanley's formula for the Möbius number of the odd partition poset

Let $n \ge 1$ and let $P_n$ be the set of partitions of $\{0, 1, \dots, n-1\}$ all of whose blocks have odd size, together with the partition into a single block (already in $P_n$ when $n$ is odd), ordered by refinement: $\pi \le \pi'$ when every block of $\pi$ is contained in a block of $\pi'$. Its least element $\hat 0$ is the partition into singletons and its greatest element $\hat 1$ is the one-block partition. The integer-valued Möbius function $\mu$ of $P_n$ satisfies

$$\mu(\hat 0, \hat 1) = \begin{cases} (-1)^{(n-1)/2} \bigl((n-2)!!\bigr)^2 & \text{if } n \text{ is odd}, \\ (-1)^{n/2} \, (n-1) \bigl((n-3)!!\bigr)^2 & \text{if } n \text{ is even}. \end{cases}$$

Here $m!!$ is the double factorial with $0!! = 1!! = 1$, and $n - 2$ and $n - 3$ are truncated at $0$, so the formula gives $\mu(\hat 0, \hat 1) = 1$ for $n = 1$ and $-1$ for $n = 2$. For $n = 3, 4, 5$ it gives $-1$, $3$ and $9$.

## Sources

- Kenneth M. Monks, *An Elementary Proof of the Explicit Formula for the Möbius Number of the Odd Partition Poset*, J. Integer Seq. 21 (2018), Article 18.9.6, theorem attributed to Stanley (proved by Sundaram and by Wachs), <https://cs.uwaterloo.ca/journals/JIS/VOL21/Monks/monks12.tex>.
