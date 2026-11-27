# Output distribution of a sampling step

Let a monadic computation be evaluated with sampling operations answered by the sample family's distributions and oracle queries answered by $O$. The computation that samples from the $i$-th distribution of the family and continues with $k$ has output distribution

$$b \leftarrow \mathrm{dist}_i,\ \text{then the output distribution of } k(b);$$

that is, the distribution $\mathrm{dist}_i$ bound with $b \mapsto$ the output distribution of $k(b)$.
