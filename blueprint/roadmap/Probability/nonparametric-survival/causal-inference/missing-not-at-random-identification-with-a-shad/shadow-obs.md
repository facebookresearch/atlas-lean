# Shadow Obs

Let $\mathcal{Y}$ and $\mathcal{Z}$ be sets. The observed data of a full-data point $(r, y, z) \in \{\mathrm{true}, \mathrm{false}\} \times \mathcal{Y} \times \mathcal{Z}$ is the point of $\mathcal{Z} \times (\mathcal{Y} \sqcup \{\ast\})$ given by

$$\mathrm{obs}(r, y, z) = \begin{cases} (z, y) & \text{if } r = \mathrm{true}, \\ (z, \ast) & \text{if } r = \mathrm{false}. \end{cases}$$

The shadow variable $z$ is always observed, the outcome $y$ only on response; the response indicator $r$ is recovered from whether the second component lies in $\mathcal{Y}$.
