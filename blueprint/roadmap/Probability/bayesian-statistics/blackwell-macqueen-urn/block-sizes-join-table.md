# Block Sizes join Table

Let $\pi$ be a set partition of $\{0, \dots, n-1\}$, let $B$ be a block of $\pi$, and let $\pi'$ be the partition of $\{0, \dots, n\}$ obtained by seating customer $n$ at table $B$, so $B$ becomes $B \cup \{n\}$ and the other blocks are unchanged. Then the multiset of block sizes of $\pi'$ is obtained from that of $\pi$ by removing one part equal to $|B|$ and adding one part equal to $|B| + 1$:

$$\{\!\{ |C| : C \in \pi' \}\!\} = \{\!\{ |B| + 1 \}\!\} + \Bigl( \{\!\{ |C| : C \in \pi \}\!\} - \{\!\{ |B| \}\!\} \Bigr).$$
