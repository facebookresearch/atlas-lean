# Second-moment matrix and linear decodability

Let $U \in \mathbb{R}^{K \times P}$ hold the true activity of $P$ measurement channels in $K$ experimental conditions, so that row $u_{i,\cdot}$ is the activity pattern of condition $i$ and column $u_{\cdot,j}$ is the activity profile of channel $j$. The second-moment matrix of the activity profiles is

$$G = \frac{1}{P}\sum_{j=1}^{P} u_{\cdot,j}\, u_{\cdot,j}^{\mathsf T} = \frac{U U^{\mathsf T}}{P}. \tag{2}$$

**Decodability.** For a feature $f \in \mathbb{R}^K$ (one value per condition) the linear read-out of condition $i$ with weights $v \in \mathbb{R}^P$ is $\hat f_i = u_{i,\cdot} v$ (Eq. 3). With isotropic noise, the best read-out maximizes $v^{\mathsf T} U^{\mathsf T} f f^{\mathsf T} U v / v^{\mathsf T} v$, and since the non-zero eigenvalues of a product are invariant under cyclic permutation,

$$\operatorname{eig}(U^{\mathsf T} f f^{\mathsf T} U) = \operatorname{eig}(f^{\mathsf T} U U^{\mathsf T} f) = P\, f^{\mathsf T} G f, \tag{5}$$

so the quality of the best linear decoder of any feature is determined by $f^{\mathsf T} G f$ alone.

**Encoding models.** If $U = M W$ with a $K \times Q$ feature matrix $M$ and feature weights $W \in \mathbb{R}^{Q \times P}$ whose columns have a zero-mean prior with covariance $\Omega$, then

$$G = \frac{M W W^{\mathsf T} M^{\mathsf T}}{P} = M \Omega M^{\mathsf T} \tag{12}$$

(in expectation over the prior). Two feature sets with weight covariances $(M_1, \Omega_1)$ and $(M_2, \Omega_2)$ define the same representational model whenever $M_1 \Omega_1 M_1^{\mathsf T} = M_2 \Omega_2 M_2^{\mathsf T}$ (Eq. 14). Every positive semidefinite $G$ arises from an encoding model with identity weight covariance: take the columns of $M$ to be the eigenvectors $v_q$ of $G$ scaled by $\sqrt{\lambda_q}$, so that $G = M M^{\mathsf T}$ (Eq. 15).

## Expansion

The second moment discards which channel does what and where channels are located, keeping only the distribution of activity profiles; Eq. (5) shows that this is exactly the information that determines linear decoding, and more generally decodability through the noise-normalized geometry. Ridge (Tikhonov) regularization of an encoding model is equivalent to a Gaussian prior on $W$; under that prior, the encoding model is a statement about $G$, so encoding analysis compares distributions of activity profiles rather than feature sets as such. Without regularization, it compares only the subspaces spanned by the features.

## Sources

- J. Diedrichsen, N. Kriegeskorte, "Representational models: a common framework for understanding encoding, pattern-component, and representational-similarity analysis", PLoS Computational Biology 13(4) (2017) e1005508, Eqs. (2)–(5), (7), (12), (14), (15), <https://doi.org/10.1371/journal.pcbi.1005508> (PMC5421820).
