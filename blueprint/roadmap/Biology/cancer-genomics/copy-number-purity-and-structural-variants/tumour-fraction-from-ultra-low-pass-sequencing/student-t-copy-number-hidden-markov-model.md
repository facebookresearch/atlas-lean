# Student-t hidden Markov model for tumour fraction from low-coverage coverage data

Let the genome be divided into $T$ equal-sized bins and let $l_1, \dots, l_T$ be the observed log copy ratios of read counts in those bins. Let $K$ be a finite set of copy-number states, each state $g \in K$ carrying an integer copy number $c_g$ and a flag for whether it is clonal or subclonal; a hidden chain $G_1, \dots, G_T$ on $K$ labels the bins.

**Emission.** Conditional on $G_t = g$,

$$p(l_t \mid G_t = g) = \mathrm{St}(l_t \mid \mu_g, \lambda_g, \nu_g),$$

a Student-$t$ density with location $\mu_g$, precision $\lambda_g$ and degrees of freedom $\nu_g$ held fixed at $2.1$. The location is not free: it is the [mixture log copy ratio](mixture-copy-ratio-of-a-subclonal-event.md)

$$\mu_g = \log \frac{2n + 2s(1 - n) + (1 - s)(1 - n) c_g}{2n + (1 - n)\phi},$$

tying every state to the two global parameters, the non-tumour proportion $n$ and the average tumour ploidy $\phi$ (with $s = 0$ at clonal states).

**Transition.** The chain is homogeneous with

$$p(G_t = j \mid G_{t-1} = i) = A_{ij}, \qquad A_{ij} = \begin{cases} e, & i = j, \\ \dfrac{1 - e}{|K| - 1}, & i \ne j, \end{cases}$$

and $e$ close to one, which penalizes state changes and so enforces long segments.

**Priors and inference.** Beta priors on $n$ and $s$, a Gamma prior on $\phi$, Gamma priors on the precisions $\lambda_g$, and Dirichlet priors on $A$ and on the initial distribution $\pi$ make the model a Bayesian hidden Markov model; the parameters $\theta = (\mu_{1:K}, \lambda_{1:K}, A, \pi, n, \phi)$ are fitted by expectation–maximization, the E step running the forward–backward recursion for the posteriors $p(G_t = g \mid l_{1:T}, \theta)$ and the M step taking the maximum a posteriori update, iterated until the penalized complete-data log likelihood changes by less than $0.1\%$. The Viterbi path then gives the segmentation, and the fitted $1 - n$ is the tumour fraction.

**Multiple restarts.** The penalized likelihood is multimodal in $(n, \phi)$, so the fit is repeated over a grid of initializations and the solution of maximal converged objective is kept; solutions in which more than half the genome is subclonal, or more than $70\%$ of calls are subclonal, are rejected as artefacts of the clonal/subclonal non-identifiability.

## Depends on

- [Mixture copy ratio of a subclonal copy-number event](mixture-copy-ratio-of-a-subclonal-event.md)

## Expansion

Two modelling choices carry the weight. The heavy-tailed emission with $\nu_g = 2.1$ gives a density whose variance is barely finite, so bins whose coverage is distorted by mappability or by a focal event not in the state space contribute bounded influence to the parameter updates, which matters at ultra-low coverage where per-bin counts are small and outliers common. The near-diagonal transition matrix with a single parameter $e$ is the discrete analogue of a segmentation penalty: the prior probability of a configuration with $k$ change points is proportional to $e^{T-k}\big((1-e)/(|K|-1)\big)^{k}$, so each change point costs a fixed factor and the Viterbi path is the maximum-likelihood segmentation under a per-break penalty $\log\big(e(|K|-1)/(1-e)\big)$. Because every state's mean is a function of the same $(n, s, \phi)$, the tumour fraction is estimated from the spacing of the observed ratio levels rather than from any single segment, which is what makes a genome-wide fit possible when no individual bin is informative.

## Sources

- V. A. Adalsteinsson, G. Ha, S. S. Freeman et al., "Scalable whole-exome sequencing of cell-free DNA reveals high concordance with metastatic tumors", Nature Communications 8 (2017), 1324, Methods ("ichorCNA: copy number prediction and tumor fraction estimation": state, emission, transition, prior, learning and inference, multiple restarts), <https://doi.org/10.1038/s41467-017-00965-y>, PMCID PMC5673918.
