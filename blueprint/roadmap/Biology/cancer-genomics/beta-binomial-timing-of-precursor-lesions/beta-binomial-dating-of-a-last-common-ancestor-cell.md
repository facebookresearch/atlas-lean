# Beta-binomial dating of a last common ancestor cell from shared mutations

**Setting.** Two lesions from one patient, a precursor $j$ (for example a tubal intraepithelial carcinoma) and a later lesion $k$ (an ovarian carcinoma or metastasis) diagnosed at age $t_k$, descend from a common ancestral cell born at unknown age $t_j < t_k$. Somatic passenger mutations (sequence and structural) accumulate along the cell lineage at a constant rate per unit time (constant mutation rate per division and constant cell-cycle length). Let $n_k$ be the number of somatic mutations in the founder cell of lesion $k$ and $n_j$ the number of those that are also present in lesion $j$ (accumulated before the common ancestor).

**Model.** Under the constant-rate assumption, each of the $n_k$ mutations arose at a time uniform on $[0, t_k]$ independently, so

$$n_j \mid n_k, t_j \sim \mathrm{Binomial}\big(n_k,\ t_j/t_k\big).$$

With a conjugate prior $t_j/t_k \sim \mathrm{Beta}(a, b)$,

$$t_j/t_k \mid n_j, n_k \sim \mathrm{Beta}\big(a + n_j,\ b + n_k - n_j\big),$$

so the posterior mean birth age of the common ancestor is

$$\mathbb{E}[t_j \mid n_j, n_k] = t_k\, \frac{a + n_j}{a + b + n_k},$$

and credible intervals for $t_j$ and for the interval $t_k - t_j$ are obtained from Beta quantiles (highest posterior density).

**Properties.**

1. As $n_k \to \infty$ with $n_j/n_k \to f$, the posterior concentrates at $t_j = f\,t_k$, the molecular-clock estimate; the prior acts like $a$ shared and $b$ private pseudo-mutations.
2. For three lesions in a linear order $j \to k \to l$, the posterior of $t_k/t_l$ is computed first from lesions $k$ and $l$, and the posterior of $t_j$ is obtained by integrating the conditional Beta posterior for $t_j/t_k$ over the posterior of $t_k$, propagating uncertainty in the intermediate time.

## Expansion

If the arrival times of the mutations carried by the founder of $k$ form a homogeneous Poisson process on $[0, t_k]$, then given their number $n_k$ they are i.i.d. uniform, and each predates $t_j$ with probability $t_j/t_k$; mutations predating the common ancestor are exactly those shared with lesion $j$ (ignoring loss and sampling error), giving the binomial likelihood. Beta–binomial conjugacy gives the posterior. A prior centred at $0.95$ with $a = 34$, $b = 1.6$, derived from the fraction of primary-tumour mutations found in metastases in earlier work, corresponds to one pseudo-patient with 34 shared and 1.6 additional mutations. Applied to high-grade serous ovarian carcinoma with tubal precursors, the analysis places a window of several years (on average about 6.5) between the precursor and ovarian carcinoma initiation, followed by rapid metastatic spread; the conclusions depend on the constant-rate assumption, which may fail if the mutation rate accelerates during progression.

## Sources

- Labidi-Galy SI, Papp E, Hallberg D, Niknafs N, Adleff V, Noe M, Bhattacharya R, Novak M, Jones S, Phallen J, Hruban CA, et al., "High grade serous ovarian carcinomas originate in the fallopian tube" (2017), Results, "Evolutionary timeline of ovarian cancer development", and Methods, "Estimating an evolutionary timeline" (following Jones et al. 2008), <https://doi.org/10.1038/s41467-017-00962-1>, PMCID PMC5653668.
- S. Jones et al., "Comparative lesion sequencing provides insights into tumor evolution", Proceedings of the National Academy of Sciences USA 105 (2008) 4283–4288, <https://doi.org/10.1073/pnas.0712345105>.
