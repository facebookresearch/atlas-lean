# Reassignment mixture model for multi-mapped fragments

**Setting.** Fragments $f_1, \dots, f_N$ originate from transcripts $t_0, t_1, \dots, t_K$, where $t_1, \dots, t_K$ are annotated (for instance transposable-element loci) and $t_0$ collects fragments from unannotated sequence. For each fragment let $q_{ij} = \Pr(f_i \mid G_i = t_j) \ge 0$ be a mapping quality derived from the alignment score ($q_{ij} = 0$ if $f_i$ does not align to $t_j$), and let $y_i = 1$ if $f_i$ aligns to more than one transcript, $y_i = 0$ otherwise. The parameters are the fragment proportions $\pi = (\pi_0, \dots, \pi_K)$ and the reassignment weights $\theta = (\theta_0, \dots, \theta_K)$, both in the probability simplex. A fragment contributes the likelihood factor

$$\Pr(f_i \mid \pi, \theta) \propto \sum_{j=0}^K \pi_j\, \theta_j^{\,y_i}\, q_{ij},$$

so $\theta$ reweights only ambiguous fragments. With latent membership weights $x_{ij}$ ($\sum_j x_{ij} = 1$), the complete-data likelihood is $\prod_i \prod_j (\pi_j \theta_j^{y_i} q_{ij})^{x_{ij}}$, and pseudo-count priors $a_j, b_j \ge 0$ are added for $\pi$ and $\theta$.

**Proposition (EM updates).** Starting from any $\pi, \theta$ with positive entries, iterate

- E-step: $\displaystyle \hat x_{ij} = \frac{\pi_j\, \theta_j^{y_i}\, q_{ij}}{\sum_{k=0}^K \pi_k\, \theta_k^{y_i}\, q_{ik}}$;
- M-step: $\displaystyle \pi_j \leftarrow \frac{\sum_i \hat x_{ij} + a_j}{\sum_{i,k} \hat x_{ik} + \sum_k a_k}, \qquad \theta_j \leftarrow \frac{\sum_i \hat x_{ij}\, y_i + b_j}{\sum_i y_i + \sum_k b_k}$.

Then:

1. The M-step outputs lie in the simplex, and a fragment aligning to a single transcript $t_j$ always has $\hat x_{ij} = 1$.
2. Each M-step maximizes $\sum_{i,j} \hat x_{ij}\left(\log \pi_j + y_i \log \theta_j\right) + \sum_j a_j \log \pi_j + \sum_j b_j \log \theta_j$ over the simplex, so each iteration does not decrease the penalized objective

$$\ell(\pi, \theta) = \sum_{i=1}^N \log \sum_{j=0}^K \pi_j\, \theta_j^{y_i}\, q_{ij} + \sum_j a_j \log \pi_j + \sum_j b_j \log \theta_j .$$

3. If $q_{i\cdot}$ is the same for all transcripts an ambiguous fragment hits, its posterior assignment is proportional to $\pi_j \theta_j$, so ambiguous fragments are pulled toward loci that are supported by uniquely aligned fragments.

## Expansion

(1): the numerators of the M-step are non-negative and sum to the denominators; for a uniquely aligned fragment only one $q_{ij}$ is non-zero. (2): the M-step objective separates into a $\pi$ part and a $\theta$ part, each of the form $\sum_j w_j \log p_j$ on the simplex, maximized by $p_j \propto w_j$ (Gibbs' inequality). The E-step weights are the posterior responsibilities, and Jensen's inequality applied to $\log \sum_j \hat x_{ij} \cdot (\pi_j \theta_j^{y_i} q_{ij}/\hat x_{ij})$ gives the usual minorization, so the standard EM ascent argument applies even though $\pi_j \theta_j$ does not sum to one over $j$. Convergence to a stationary point follows from Wu's conditions; an informative prior $b_j$ keeps $\theta$ away from the boundary in highly repetitive genomes. After convergence each fragment is assigned to its maximum-posterior transcript, or discarded when no posterior exceeds a threshold, which is what lets the method quantify individual proviral loci rather than whole repeat families.

## Sources

- M. L. Bendall, M. de Mulder, L. P. Iñiguez, A. Lecanda-Sánchez, M. Pérez-Losada, M. A. Ostrowski, et al., "Telescope: Characterization of the retrotranscriptome by accurate estimation of transposable element expression", PLoS Computational Biology 15 (2019) e1006453, Methods, "Fragment reassignment mixture model" and "Parameter estimation and fragment reassignment by EM", <https://doi.org/10.1371/journal.pcbi.1006453> (PMC6786656).
- A. P. Dempster, N. M. Laird, D. B. Rubin, "Maximum likelihood from incomplete data via the EM algorithm", Journal of the Royal Statistical Society Series B 39 (1977) 1–38, <https://doi.org/10.1111/j.2517-6161.1977.tb01600.x>.
