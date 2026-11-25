# Mutual Info

Let $\alpha$ and $\beta$ be finite types and let $p$ be a probability mass function on $\alpha \times \beta$, with marginals $p_X(x) = \sum_{y} p(x, y)$ and $p_Y(y) = \sum_{x} p(x, y)$. The mutual information of $p$ in nats is the mutual information in bits multiplied by $\ln 2$:

$$I_{\mathrm{nats}}(p) = I_{\mathrm{bits}}(p) \cdot \ln 2,$$

where $I_{\mathrm{bits}}(p) = D_{\mathrm{KL}}(p \parallel p_X \otimes p_Y) / \ln 2$ is the bits mutual information of the joint law, so that $I_{\mathrm{nats}}(p) = D_{\mathrm{KL}}(p \parallel p_X \otimes p_Y)$.
