# GEM M-step with a k-mer positional prior

In a genomic region with candidate binding events at base positions $1, \dots, M$ and mapped reads $r_1, \dots, r_N$, model each read as drawn from the mixture

$$p(r_n \mid \pi) = \sum_{m=1}^{M} \pi_m\, p(r_n \mid m),$$

where $p(r_n \mid m)$ is the empirical read spatial distribution around event $m$ and $\pi$ lies in the probability simplex. Place on $\pi$ the negative Dirichlet prior

$$p(\pi) \propto \prod_{m=1}^{M} \pi_m^{-\alpha_s + \alpha_m},$$

with a uniform sparseness parameter $\alpha_s > 0$ and event-specific parameters $0 \le \alpha_m < \alpha_s$ proportional to the positional prior count $C_m$, the number of bound sequences containing an enriched k-mer whose expected binding offset maps to position $m$ (scaled by a tuning parameter $0 \le \mu < 1$). With E-step responsibilities $\gamma(z_n = m) = \pi_m p(r_n \mid m) / \sum_{m'} \pi_{m'} p(r_n \mid m')$ and effective read counts $N_m = \sum_n \gamma(z_n = m)$, GEM's M-step update (equivalently, the maximizer of the truncated objective $\sum_m \max(0, N_m - \alpha_s + \alpha_m)\log \pi_m$ over the simplex, provided $N_m > \alpha_s - \alpha_m$ for at least one $m$) is

$$\hat\pi_m = \frac{\max(0,\; N_m - \alpha_s + \alpha_m)}{\sum_{m'} \max(0,\; N_{m'} - \alpha_s + \alpha_{m'})},$$

and events with $\hat\pi_m = 0$ are removed from the model.

## Depends on

- [The GPS M-step with component elimination](m-step.md)

## Expansion

The untruncated negative-Dirichlet objective $\sum_m (N_m - \alpha_s + \alpha_m) \log \pi_m$ is unbounded above as $\pi_m \to 0$ whenever $N_m < \alpha_s - \alpha_m$, so GEM truncates negative weights to zero before normalizing, giving the maximizer of $\sum_m \max(0, N_m - \alpha_s + \alpha_m) \log \pi_m$. This update is the GPS M-step with the event-dependent pseudo-count $\alpha_s - \alpha_m$ in place of the uniform one: the read count of an event is reduced by $\alpha_s$ for sparseness and increased by $\alpha_m$ when the sequence at $m$ matches the discovered motif. Because $\alpha_m < \alpha_s$, the net penalty stays positive, so a motif-supported position without enough read support is still eliminated, while an event without motif support survives if its reads alone exceed $\alpha_s$. GEM alternates this event prediction with k-mer motif discovery on the improved event positions, which sharpens the spatial resolution of predicted binding events.

## Sources

- Y. Guo, S. Mahony and D. K. Gifford, "High resolution genome wide binding event finding and motif discovery reveals transcription factor spatial binding constraints", *PLoS Computational Biology* 8 (2012), e1002638, Methods sections "Positional prior generation" and "Binding event prediction with a positional prior", <https://doi.org/10.1371/journal.pcbi.1002638> (PMC3415389).
