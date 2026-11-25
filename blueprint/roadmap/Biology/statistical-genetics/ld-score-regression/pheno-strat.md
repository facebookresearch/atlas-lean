# Phenotype with population stratification

In an [LD-score model](model.md) with effects $\beta_k$ and noise $\varepsilon_i$, for a real $N \times M$ genotype matrix $X$, a real number $s$ and a stratification axis $c \in \mathbb{R}^N$, the stratified phenotype of individual $i$ is the function

$$y_i = \sum_{k=1}^{M} X_{ik} \beta_k + \varepsilon_i + s\, c_i$$

on $\Omega$: the [phenotype](pheno.md) plus a fixed non-genetic shift along $c$ (for example a mean difference between ancestry groups).
