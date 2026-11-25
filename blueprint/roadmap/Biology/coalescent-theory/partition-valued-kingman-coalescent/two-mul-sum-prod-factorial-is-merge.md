# Splitting identity

For every partition $\pi' \in \mathcal{P}_n$,

$$2 \sum_{\pi} \prod_{B \in \pi} |B|! = (n - |\pi'|) \prod_{B \in \pi'} |B|!,$$

where the sum runs over the partitions $\pi$ from which $\pi'$ [arises by merging two blocks](is-merge.md). A block of size $b$ splits into two blocks in $(2^b - 2)/2$ ways, and $\sum_{\emptyset \ne A \subsetneq B} |A|!\,|B \setminus A|! = (b-1)\, b!$.
