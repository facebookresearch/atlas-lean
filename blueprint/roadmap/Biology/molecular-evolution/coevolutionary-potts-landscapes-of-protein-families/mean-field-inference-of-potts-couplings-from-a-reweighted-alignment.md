# Mean-field inference of Potts couplings from a reweighted alignment

Let an alignment contain $M$ sequences $(a^m_1, \dots, a^m_L)$ over $q$ symbols. To reduce
phylogenetic redundancy, weight sequence $m$ by

$$w_m = \Big(1 + \sum_{m' \ne m} \theta\big((1-\vartheta) L - d_{mm'}\big)\Big)^{-1},$$

where $d_{mm'}$ is the number of mismatches between sequences $m$ and $m'$, $\theta$ is the
Heaviside step function and $\vartheta \in (0,1)$ is an identity threshold (for example
$\vartheta = 0.8$), so $w_m$ is the inverse number of sequences (including $m$) sharing at least a fraction $\vartheta$ of identical positions with $m$. With
$M_{\mathrm{eff}} = \sum_m w_m$ and pseudocount weight $\lambda \in [0,1)$, the regularized
frequencies are

$$f_i^{\lambda}(a) = \frac{\lambda}{q} + \frac{1-\lambda}{M_{\mathrm{eff}}}\sum_{m=1}^{M} w_m\,
\delta_{a_i^m, a}, \qquad
f_{ij}^{\lambda}(a,b) = \frac{\lambda}{q^2} + \frac{1-\lambda}{M_{\mathrm{eff}}}\sum_{m=1}^{M}
w_m\, \delta_{a_i^m, a}\,\delta_{a_j^m, b}.$$

Let $C_{ij}(a,b) = f_{ij}^{\Lambda_2}(a,b) - f_i^{\Lambda_2}(a) f_j^{\Lambda_2}(b)$ be the connected
correlation matrix over non-gap symbols, computed with a large pseudocount $\Lambda_2$. The
mean-field approximation to the
[Potts model](potts-model-of-a-protein-family-and-context-dependent-mutational-effects.md)
$P \propto \exp\{\sum_i \varphi_i + \sum_{i < j}\varphi_{ij}\}$ sets the couplings of distinct
sites $i \ne j$ to the negative inverse correlation matrix,

$$\varphi_{ij}(a,b) = -\big[C^{-1}\big]_{ij}(a,b) \qquad (i \ne j),$$

with couplings involving the gap symbol set to zero (since $C$ is symmetric, so is $C^{-1}$, and
$\varphi_{ji}(b,a) = \varphi_{ij}(a,b)$), and the fields, with a small pseudocount $\Lambda_1$, to

$$\varphi_i(a) = \log\frac{f_i^{\Lambda_1}(a)}{f_i^{\Lambda_1}(-)} - \sum_{j \ne i}\sum_{b}\varphi_{ij}(a,b)\,
f_j^{\Lambda_1}(b).$$

## Depends on

- [Potts model of a protein family and context-dependent mutational effects](potts-model-of-a-protein-family-and-context-dependent-mutational-effects.md)

## Expansion

Maximum-likelihood fitting of a Potts model requires the partition function, which is a sum over
$q^L$ sequences. The mean-field (small-coupling) expansion instead matches the model's connected
two-point correlations to the data to first order, giving couplings equal to minus the inverse of
the correlation matrix, and the fields then follow from the single-site marginals. The gap symbol
is the reference state that fixes the gauge, which is why it has no couplings and appears in the
denominator of the field formula. The correlation matrix is singular without regularization, and
the source uses a large pseudocount ($\Lambda_2 = 0.5$) to counter the systematic bias of the
mean-field approximation, but the Bayesian-size pseudocount $\Lambda_1 = 1/M_{\mathrm{eff}}$ for the
fields. The source writes the step function on the distance directly and prints the coupling formula without the minus sign; the forms above are the standard ones for identity-threshold reweighting, and for couplings the sign depends on whether
the Potts energy enters the exponent with a plus or a minus. The source also lets $i = j$ in the
couplings and in the field sum; the diagonal blocks of $C^{-1}$ are not used here, matching the
restriction of the Potts couplings to distinct sites.

## Sources

- M. Figliuzzi, H. Jacquier, A. Schug, O. Tenaillon, M. Weigt, "Coevolutionary landscape inference
  and the context-dependence of mutations in beta-lactamase TEM-1", Molecular Biology and Evolution
  33 (2016) 268-280, Materials and Methods, "Details of Statistical Inference" (Eqs. 12-17),
  <https://doi.org/10.1093/molbev/msv211> (PMC4693977).
