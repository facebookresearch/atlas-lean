# W-dependent part of the ARD-NMF objective

For a real $\phi$, real matrices $V, H, W$ and relevances $\lambda_k$, put

$$C_W(W) = \frac{D_1(V \mid WH)}{\phi} + \sum_{k \in K} \sum_{f \in F} \frac{w_{fk}}{\lambda_k},$$

where $D_1$ is the [data-fit term](data-fit.md), with the convention $x/0 = 0$.
