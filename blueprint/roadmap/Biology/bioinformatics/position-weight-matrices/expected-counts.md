# Expected letter counts in motif columns

For sequences $x^{(1)}, \dots, x^{(N)}$ of length $n + w$, a positive matrix $\theta$, a column $i$ and a letter $b$, the expected count is

$$c_i(b) = \sum_{m} \sum_{z} P(z \mid x^{(m)}, \theta)\, [\,z \text{ has a start } j \text{ and } x^{(m)}_{j+i} = b\,],$$

with $P$ the posterior of the [motif model](motif-model.md).
