# Joint background selection and hitchhiking model of neutral diversity

Let the genome be divided into windows $i$ with recombination rate $r_i$ per base pair and functional density $fd_i$ (the fraction of the genome's selected sites lying in window $i$). Model background selection (BGS) as a reduction of the local effective size by the factor $e^{-G_i}$, where $G_i\ge0$ sums, over windows $k$, the contributions of deleterious mutations with genomic rate $U$, density $fd_k$ and heterozygous effect $sh$, attenuated by genetic distance through terms $sh+P|M_i-M_k|$ and $sh+P|M_i-M_{k+1}|$ ($M$ in Morgans, $P$ the index of panmixis accounting for selfing). Model recurrent selective sweeps with Coop and Ralph's hitchhiking coalescence rate, the sweep rate being split among windows in proportion to $fd_i$. The expected neutral pairwise diversity in window $i$ is then

$$\mathbb E[\pi_i]=\frac{\theta_{\mathrm{neutral}}}{e^{G_i}+\alpha\,fd_i/r_i},\qquad \alpha=2N\,V\,J_{2,2},$$

where $\theta_{\mathrm{neutral}}$ is diversity without linked selection, $V$ the genome-wide rate of sweeps and $J_{2,2}$ the probability that a sweep forces two linked lineages to coalesce, as defined by Coop and Ralph. The special cases $\alpha=0$ (BGS only, $\mathbb E[\pi_i]=\theta_{\mathrm{neutral}}e^{-G_i}$), $G_i=0$ (hitchhiking only) and $\alpha=G_i=0$ (neutrality) are nested models.

## Remarks

Pairwise diversity is $\theta$ times the expected pairwise coalescence time relative to the neutral one. BGS rescales the drift coalescence rate $1/(2N)$ to $e^{G}/(2N)$, while sweeps add an extra coalescence rate proportional to the sweep rate and inversely proportional to recombination; adding the two rates and inverting gives the denominator. The model predicts the positive correlation between recombination rate and diversity, and its strength measures how much linked selection removes neutral variation. Fitted across species, this removal is stronger in species with large census sizes, which helps explain why neutral diversity varies far less across species than census size.

## Depends on

- [Background selection on a uniformly recombining chromosome](background-selection-on-a-uniformly-recombining-chromosome.md)

## Sources

- R. B. Corbett-Detig, D. L. Hartl, T. B. Sackton, "Natural selection constrains neutral diversity across a wide range of species", PLoS Biol. 13 (2015) e1002112, Materials and Methods, section 4, Equations (1)–(3), <https://doi.org/10.1371/journal.pbio.1002112>, PMCID PMC4393120.
