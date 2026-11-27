# The weighted majority vote

For weights $P_1, \dots, P_k$ on hypotheses $h_1, \dots, h_k$ with Boolean values, the weighted majority vote at a point $x$ is $\mathrm{true}$ exactly when the hypotheses voting $\mathrm{true}$ carry more than half of the total weight:

$$\operatorname{vote}_P(x) = \mathbf{1}\Big[\tfrac12 \sum_j P_j < \sum_{j : h_j(x) = \mathrm{true}} P_j\Big].$$
