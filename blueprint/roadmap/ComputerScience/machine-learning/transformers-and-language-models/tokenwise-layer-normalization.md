# Tokenwise layer normalization

For a single token vector $x\in\mathbb R^d$, $d\ge1$, form the feature mean $\mu=d^{-1}\sum_j x_j$ and variance $v=d^{-1}\sum_j(x_j-\mu)^2$. Given learned vectors $\gamma,\beta\in\mathbb R^d$ and a fixed $\epsilon>0$, set

$$\operatorname{LN}(x)_i=\gamma_i\frac{x_i-\mu}{\sqrt{v+\epsilon}}+\beta_i.$$

The same parameters are used at every token; the statistics use neither other tokens nor other examples in the batch. A constant input has output $\beta$, including when $d=1$.

## Sources

- Ba, Kiros and Hinton, [*Layer Normalization*](https://arxiv.org/abs/1607.06450) (2016), §3; the positive denominator stabilizer is specified in the [PyTorch 2.12 LayerNorm specification](https://docs.pytorch.org/docs/2.12/generated/torch.nn.LayerNorm.html).
