# Single-head scaled dot-product attention

For $n$ tokens $X_j \in \mathbb{R}^d$, query and key matrices $W_Q, W_K \in \mathbb{R}^{d \times d_k}$ with $d_k \ne 0$, and value matrix $W_V \in \mathbb{R}^{d \times d_v}$, the output for token $i$ is $\sum_j a_{ij} X_j W_V$, where $(a_{ij})_j = \mathrm{softmax}_j\big(\langle X_i W_Q, X_j W_K\rangle / \sqrt{d_k}\big)$ are the attention weights of token $i$.
