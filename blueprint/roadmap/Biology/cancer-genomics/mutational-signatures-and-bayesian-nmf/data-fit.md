# Data-fit term of the ARD-NMF objective

For real matrices $V$ ($F \times N$), $W$ ($F \times K$) and $H$ ($K \times N$), the data-fit term is

$$D_1(V \mid WH) = \sum_{f \in F} \sum_{n \in N} d\bigl(v_{fn} \mid (WH)_{fn}\bigr),$$

where $d$ is the [generalized Kullback–Leibler divergence](kl-div.md) and $WH$ the [reconstruction](recon.md).
