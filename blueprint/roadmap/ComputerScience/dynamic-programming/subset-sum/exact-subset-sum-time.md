# Event count of exact subset sum

Let $x = (x_1, \dots, x_n)$ be a list of natural
numbers and $t \in \mathbb{N}$ a target. For $0 \le i \le n$ let $L_i$ be the list of attainable
sums of the prefix $(x_1, \dots, x_i)$ with target $t$. For $i < n$ let $M_i$ be the merge of
$L_i$ with the list obtained by adding $x_{i+1}$ to every entry of $L_i$, let $c_i$ be the
number of comparisons this merge makes, and let $D_i$ be $M_i$ with adjacent repeated values
deleted. Then the number of counted events of the exact subset-sum procedure on $x$ and $t$ is

$$1 + n + \sum_{i=0}^{n-1} \bigl(|L_i| + c_i + (|M_i| - 1) + |D_i|\bigr) + |L_n|,$$

where $|\cdot|$ denotes length and $|M_i| - 1$ is truncated subtraction of natural numbers.
