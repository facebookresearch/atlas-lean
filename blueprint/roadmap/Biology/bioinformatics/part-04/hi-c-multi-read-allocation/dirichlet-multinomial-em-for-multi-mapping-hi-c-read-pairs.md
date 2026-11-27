# Dirichlet–multinomial EM for multi-mapping Hi-C read pairs

Divide the genome into $M$ bins and index bin pairs by $(j, k)$ with $1 \le j < k \le M$. For each of $N$ valid Hi-C read pairs $i$, let $S_{O_i}$ be the set of bin pairs to which both ends can align, and $Y_{i,(j,k)} = \mathbf 1[(j,k) \in S_{O_i}]$; uni-reads have $|S_{O_i}| = 1$ and multi-reads $|S_{O_i}| > 1$. The latent indicator $Z_{i,(j,k)} = 1$ marks the true origin, with $\sum_{(j,k)} Z_{i,(j,k)} = 1$, and the true origin is assumed to be one of the alignable pairs. The model is

$$\mathbf Z_i \overset{\text{iid}}{\sim} \mathrm{Multinomial}\big(1; (\pi_{(j,k)})_{j<k}\big), \qquad \boldsymbol\pi \sim \mathrm{Dirichlet}\big((\gamma_{(j,k)})_{j<k}\big), \qquad \gamma_{(j,k)} = N\,\mathrm{Spline}(j,k) + 1,$$

where $\pi_{(j,k)}$ is the contact probability of bins $j, k$ and $\mathrm{Spline}(j,k)$ is a univariate spline estimate of the random-contact probability as a function of genomic distance, so $N\,\mathrm{Spline}(j,k)$ acts as pseudo-counts.

**Lemma.** Given its true origin, read $i$ shows alignments at exactly the pairs in $S_{O_i}$ with probability $1$: $\mathbb P(\mathbf Y_i \mid Z_{i,(j,k)} = 1) = 1$ for $(j,k) \in S_{O_i}$. Hence

$$\mathbb P(\mathbf Y, \mathbf Z \mid \boldsymbol\pi) = \prod_{i=1}^N \prod_{j<k} \pi_{(j,k)}^{Z_{i,(j,k)}}, \qquad \mathbb P(\boldsymbol\pi \mid \mathbf Z) \propto \prod_{j<k}\pi_{(j,k)}^{\sum_i Z_{i,(j,k)} + N\,\mathrm{Spline}(j,k)} .$$

**EM algorithm.** The maximum a posteriori contact probabilities are found by iterating

$$\text{E-step:}\quad Z^{(t)}_{i,(j,k)} = \frac{\pi^{(t)}_{(j,k)}}{\sum_{(j',k') \in S_{O_i}}\pi^{(t)}_{(j',k')}}\,\mathbf 1[(j,k) \in S_{O_i}],$$

$$\text{M-step:}\quad \pi^{(t+1)}_{(j,k)} = \frac{\sum_{i=1}^N Z^{(t)}_{i,(j,k)} + N\,\mathrm{Spline}(j,k)}{N + \sum_{j'<k'} N\,\mathrm{Spline}(j',k')} .$$

## Depends on

- [Dirichlet–multinomial conjugacy](../../../../ComputerScience/machine-learning/bayesian-inference-and-sampling/conjugate-priors/posterior-categorical-seq-kernel-dirichl.md)
- [Dirichlet distribution](../../../../Probability/distributions/continuous/dirichlet-distribution/dirichlet-law/dirichlet-measure.md)
- [Multinomial mass function](../../../../Probability/distributions/discrete/multinomial-distribution/multinomial-real.md)

## Proof depends on

- [The EM inequality](../../../../ComputerScience/machine-learning/bayesian-inference-and-sampling/expectation-maximization-algorithm/em-q-sub-le-log-lik-sub.md)

## Expansion

The E-step distributes each multi-read across its alignable bin pairs in proportion to current contact probabilities; uni-reads keep weight one. The M-step is the Dirichlet–multinomial posterior mode, blending local interaction evidence with the distance-decay prior, which prevents multi-reads from being absorbed entirely by already dense bin pairs. The final posterior probabilities $\mathbb P(Z_{i,(j,k)} = 1 \mid \mathbf Y_i, \boldsymbol\pi)$ assign each multi-read to its most probable bin pair, retaining it only when that probability exceeds $0.5$, which keeps the output compatible with standard significant-interaction callers.

## Sources

- Y. Zheng, F. Ay, S. Keleş, "Generative modeling of multi-mapping reads with mHi-C advances analysis of Hi-C studies", eLife 8 (2019) e38070, Materials and methods ("mHi-C generative model and parameter estimation"), Eqs. 1–2 and Lemma 1, <https://doi.org/10.7554/eLife.38070>, PMCID PMC6450682.
