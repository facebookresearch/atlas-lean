# Normalization of the composite score model

Let a [composite-score model](composite-model.md) with prior $\pi$ have finite value sets $\Sigma_i$ and normalized score functions: $\sum_{y \in \Sigma_i} s_i(y) = 1$ and $\sum_{y \in \Sigma_i} n_i(y) = 1$ for every $i$. Then

$$\sum_{z \in \Sigma_1 \times \dots \times \Sigma_k} \Bigl(\pi \prod_i s_i(z_i) + (1 - \pi) \prod_i n_i(z_i)\Bigr) = 1,$$

so the joint model is a probability distribution on observations and the [normalized composite score](posterior.md) is a genuine posterior probability.
