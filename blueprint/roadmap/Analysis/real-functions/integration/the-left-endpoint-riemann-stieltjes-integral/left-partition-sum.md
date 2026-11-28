# Net of left-endpoint partition sums

For $f, h : \mathbb{R} \to \mathbb{R}$ and $a, b \in \mathbb{R}$, the left-endpoint partition sums of $f$ against $h$ form a net indexed by the finite sets $s \subseteq \mathbb{R}$, ordered by inclusion: the sum attached to $s$ is $\sum f(u)\,(h(x) - h(u))$ over the consecutive points $u < x$ of $\{a, b\} \cup \{x \in s : a < x < b\}$.

The partitions are those of the point sets formed by inserting both endpoints $a$ and $b$ into the points of a finite set that lie strictly between $a$ and $b$, ordered increasingly. For $a > b$ the interval $[a, b]$ is empty and every such point set is $\{b, a\}$, with the single cell $(b, a]$; the sums are then not those of an oriented integral. For example, from $a = 1$ to $b = 0$ with $f = 1$ and $h(x) = x$ the left-endpoint sum is $h(1) - h(0) = +1$, not $-1$ and not the empty sum.
