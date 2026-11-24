# At fixed latent values the visits are independent log-normals

Let `n` visits have log-scale means `m j` (real numbers) and log-scale variances `v j ≥ 0`: the mean
and the variance of the log-concentration `m j + e j`. If the visit errors `e j` are independent
centered Gaussians `N(0, v j)`, the vector of visit concentrations `exp (m j + e j)` has as law the
product of the log-normal laws, the images of `N(m j, v j)` under `exp`: the visits are independent
and each is log-normal (a point mass when `v j = 0`). In the population model the log-scale means
`m j` are those of one subject at fixed values of the latent subject parameters.
