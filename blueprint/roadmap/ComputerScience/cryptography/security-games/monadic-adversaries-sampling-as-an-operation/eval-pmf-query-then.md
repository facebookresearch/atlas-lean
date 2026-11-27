# Output distribution of a query step

Let a monadic computation be evaluated with sampling operations answered by the sample family's distributions and oracle queries answered by $O$. The computation that asks the oracle query $a$ and continues with $k$ has output distribution

$$b \leftarrow O(a),\ \text{then the output distribution of } k(b);$$

that is, the distribution $O(a)$ bound with $b \mapsto$ the output distribution of $k(b)$.
