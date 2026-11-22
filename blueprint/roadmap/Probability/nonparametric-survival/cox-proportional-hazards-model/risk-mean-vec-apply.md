# Components of the weighted mean covariate vector

Component $j$ of the weighted mean covariate vector $\bar x_i(\beta)$ is the weighted mean of the $j$-th
covariate over the risk set of subject $i$:

$$\bar x_i(\beta)_j = \frac{\sum_{l \in R(T_i)} x_{l,j} \, e^{\langle \beta, x_l \rangle}}{\sum_{l \in R(T_i)} e^{\langle \beta, x_l \rangle}}.$$
