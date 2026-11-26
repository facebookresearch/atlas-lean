# Huber group lasso for shared-topology gene regulatory networks

**Linear GRN model.** For $p$ genes with mRNA concentrations $\mathbf x \in \mathbb R^p$, take

$$\dot{\mathbf x} = C\mathbf x + S\mathbf r, \qquad \mathbf r = F\mathbf x, \qquad\text{so}\qquad \dot{\mathbf x} = C\mathbf x + M\mathbf x,\quad M = SF,$$

where $C = \operatorname{diag}(-c_1,\dots,-c_p)$ with degradation rates $c_i > 0$, $S \in \mathbb R^{p\times m}$ is the stoichiometric matrix and $\mathbf r$ the reaction rates. Gene $j$ regulates gene $i$ iff $m_{ij} \neq 0$. Zero-order-hold sampling with step $\Delta t$ gives

$$\mathbf x_k = A\mathbf x_{k-1}, \qquad A = e^{C\Delta t} + C^{-1}\big(e^{C\Delta t} - I\big)M .$$

Both $e^{C\Delta t}$ and $C^{-1}(e^{C\Delta t} - I)$ are diagonal with positive diagonal entries, so the off-diagonal entries of $A$ have exactly the zero/nonzero pattern of $M$: the network topology (ignoring self-regulation) is the off-diagonal support of $A$.

**Multiple datasets.** Given $m$ time courses $\tilde X^{(k)} \in \mathbb R^{p\times(n_k+1)}$, $k = 1,\dots,m$, of the same network under different conditions,

$$Y^{(k)} = A^{(k)}X^{(k)} + E^{(k)},$$

with $X^{(k)}$ the first $n_k$ and $Y^{(k)}$ the last $n_k$ columns. The matrices $A^{(k)}$ may differ in value but must share one zero pattern.

**Huber group lasso.** With the Huber loss

$$H_\delta(\theta) = \begin{cases} \theta^2, & |\theta| \le \delta,\\ 2\delta|\theta| - \delta^2, & \text{otherwise},\end{cases}$$

dataset weights $w_k = n_k/\sum_l n_l$, rows $A_i^{(k)\mathsf T}$ and columns $\mathbf x_j^{(k)}$ of $X^{(k)}$, estimate

$$\min_{A^{(1)},\dots,A^{(m)}}\ \sum_{i=1}^{p}\sum_{k=1}^{m} w_k\sum_{j=1}^{n_k} H_\delta\big(y_{ij}^{(k)} - A_i^{(k)\mathsf T}\mathbf x_j^{(k)}\big) + \lambda\sum_{i=1}^{p}\sum_{\ell=1}^{p}\sqrt{\big(a_{i\ell}^{(1)}\big)^2 + \dots + \big(a_{i\ell}^{(m)}\big)^2}.$$

Replacing $H_\delta(\theta)$ by $\theta^2$ gives the (squared-error) group lasso. The group penalty makes each edge's $m$ strengths $b_{i\ell} = (a_{i\ell}^{(1)},\dots,a_{i\ell}^{(m)})^{\mathsf T}$ all zero or all nonzero, which enforces a common topology. The problem separates over target genes $i$: each is a convex block-penalized robust regression

$$J(\mathbf b) = \sum_{j=1}^{n}\omega_j H_\delta\big(y_j - \mathbf x_j^{\mathsf T}\mathbf b\big) + \lambda\sum_{\ell=1}^{p}\|\mathbf b_\ell\|_2, \qquad n = \sum_k n_k,$$

where the stacked design is block diagonal over datasets and $\omega_j$ is the weight of the dataset that observation $j$ comes from.

**Path and robustness tuning.** $\lambda_{\max} = \max_{i,\ell}\big\|\sum_j\omega_j H_\delta'(y_{ij})\,\mathbf x_{j,\ell}\big\|_2$ is the smallest $\lambda$ giving the empty network, and solutions are computed down to $0.01\lambda_{\max}$. The Huber threshold is $\delta = \max(1.345\,\hat\sigma, 1)$ with $\hat\sigma = \mathrm{MAD}/0.6745$ from least-absolute-deviation residuals.

**Stability-selection edge scores.** Draw $N$ moving-block bootstrap replicates of every dataset (blocks $j,\dots,j+l-1$ of length $l$, resampled with replacement and concatenated), refit for each $\lambda$ in a grid $\Lambda$, and score edge $j\to i$ by

$$\Pi_\lambda(i,j) = \frac{\#\{b : A_\lambda^{*(b)}(i,j) \ne 0\}}{N}, \qquad \Pi(i,j) = \max_{\lambda\in\Lambda}\Pi_\lambda(i,j).$$

## Expansion

Squared loss lets a few outlying expression values dominate the fit. Huber loss coincides with it for residuals up to $\delta$ and grows only linearly beyond, which bounds the influence of outliers at small efficiency cost under Gaussian noise. Grouping across datasets pools evidence for an edge without forcing equal strengths, which suits conditions that rescale but do not rewire regulation. Moving-block resampling keeps short-range temporal dependence within each bootstrap series.

With $m = 8$ simulated datasets of $15$ time points from a $5$-gene network under Gaussian-mixture noise (variance $1$ with probability $0.8$, $10^2$ with probability $0.2$), the Huber group lasso reached AUROC and AUPR $1.0000$ against $0.9896$ and $0.9852$ for the group lasso. On the synthetic yeast IRMA network using all nine switch-on and switch-off datasets it scored AUROC $0.8438$ and AUPR $0.8049$ against $0.6302$ and $0.5122$.

## Sources

- L.-Z. Liu, F.-X. Wu, W. J. Zhang, "A group LASSO-based method for robustly inferring gene regulatory networks from multiple time-course datasets", BMC Systems Biology 8 (Suppl 3) (2014) S1, Model: Equations (1)-(5); Method: Equations (6)-(9), (24)-(25) and the Implementation subsection; Results: Tables 1-2, <https://doi.org/10.1186/1752-0509-8-S3-S1>, PMCID PMC4243122.
