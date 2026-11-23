# First step of the random-joining law from at least two blocks

Let $m$ be a natural number and $b$ a list of natural numbers with $r \ge 2$ entries. For every
list $b'$ of natural numbers and every list $\mathbf{p}'$ of block-size lists, the
[random-joining law](random-joining.md) satisfies

$$R_{m+1}\bigl(b, (b', \mathbf{p}')\bigr) = \begin{cases}
\dfrac{1}{\binom{r}{2}} \displaystyle\sum_{0 \le i < j < r} R_m\bigl(b^{(i,j)}, \mathbf{p}'\bigr)
& \text{if } b' = b, \\
0 & \text{otherwise,} \end{cases}$$

where $(b', \mathbf{p}')$ is the list of block-size lists starting with $b'$ followed by the entries
of $\mathbf{p}'$, and $b^{(i,j)}$ is the list obtained from $b$ by
[merging the blocks](merge-blocks.md) at positions $i$ and $j$: for $b' = b$ it is the average
over the $\binom{r}{2}$ pairs of positions.
