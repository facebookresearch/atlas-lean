# Additive design with batch and biological effects

Let $n$ (samples) and $p$ (features) be natural numbers and $\mathbf 1 \in \mathbb{R}^n$ the
all-ones vector. For a residual matrix $E \in \mathbb{R}^{n \times p}$, a feature-wise baseline
$\mu \in \mathbb{R}^p$, a batch covariate $b \in \mathbb{R}^n$ with batch effect
$\beta \in \mathbb{R}^p$, and a biological covariate $s \in \mathbb{R}^n$ with biological signal
$\delta \in \mathbb{R}^p$, the additive design is the $n \times p$ data matrix

$$X = E + \mathbf 1 \mu^\top + b \beta^\top + s \delta^\top, \qquad
X_{ij} = E_{ij} + \mu_j + b_i \beta_j + s_i \delta_j.$$

All arguments are arbitrary real matrices and vectors; typical covariates are $0/1$ indicators of a
batch and of a condition. The design is called confounded when $s = b$; for indicators this means
that the samples of the condition are exactly those of the batch.
