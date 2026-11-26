# Pattern-component model likelihood

Let $Y \in \mathbb{R}^{N \times P}$ be activity measurements of $P$ channels, modelled by the linear mixed model

$$Y = Z U + X B + \epsilon, \tag{6}$$

with $Z$ the $N \times K$ design matrix of the $K$ conditions, $U \in \mathbb{R}^{K \times P}$ the activity patterns, $X$ a design matrix of nuisance effects with coefficients $B$, and noise $\epsilon$ independent and identically distributed $\mathcal{N}(0, \sigma_\epsilon^2)$. In pattern-component modelling (PCM) the activity profiles (columns of $U$) are random, independent across channels, with mean zero and covariance $s\, G$, where $G$ is the second-moment matrix predicted by a representational model and $s > 0$ a signal-strength parameter. Marginalizing over $U$, each channel is

$$y_{\cdot,j} \sim \mathcal{N}\big(X b_{\cdot,j},\ V(\theta)\big), \qquad V(\theta) = Z\, s G\, Z^{\mathsf T} + \sigma_\epsilon^2 I, \qquad \theta = (s, \sigma_\epsilon^2). \tag{16}$$

With the residual-forming matrix $R = I - X (X^{\mathsf T} V^{-1} X)^{-1} X^{\mathsf T} V^{-1}$ (Eq. 17), the restricted log-likelihood is

$$l(Y \mid G, \theta) = -\frac{NP}{2}\log(2\pi) - \frac{P}{2}\log|V| - \frac{1}{2}\operatorname{trace}\big(Y^{\mathsf T} R^{\mathsf T} V^{-1} R Y\big) - \frac{P}{2}\log|X^{\mathsf T} V^{-1} X|. \tag{18}$$

Models are compared by this likelihood with $\theta$ maximized or integrated out separately for each model, since signal and noise levels vary between regions and individuals and carry no model information.

## Depends on

- [Second-moment matrix and linear decodability](second-moment-matrix-and-linear-decodability.md)

## Expansion

Because $U$ enters linearly and has a Gaussian distribution, $ZU + \epsilon$ is Gaussian with covariance $Z sG Z^{\mathsf T} + \sigma^2_\epsilon I$ for every channel; independence across channels makes the log-likelihood a sum over channels, which gives the factor $P$. Restricted maximum likelihood accounts for estimating the fixed effects $B$. Since the marginal law depends on $U$ only through $G$, PCM evaluates exactly the quantity that encoding models (through the feature matrix and weight prior) and representational similarity analysis (through distances) also constrain. When its distributional assumptions hold, PCM gives optimal model selection; in simulations, regularized encoding analysis and likelihood-based RSA came close to it.

## Sources

- J. Diedrichsen, N. Kriegeskorte, "Representational models: a common framework for understanding encoding, pattern-component, and representational-similarity analysis", PLoS Computational Biology 13(4) (2017) e1005508, Eqs. (6), (16)–(18), and Results, <https://doi.org/10.1371/journal.pcbi.1005508> (PMC5421820).
