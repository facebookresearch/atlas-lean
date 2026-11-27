# Gland-fission cellular automaton with Gaussian fitness changes

Tumour glands occupy the sites of a three-dimensional lattice ($400 \times 400 \times 400$ points in
the source). The process starts from a single gland at the centre with fitness $F = 1$ and evolves by
gland fission until the tumour reaches a target size ($8 \times 10^6$ glands, about $8 \times 10^{10}$
cells):

1. **Division and death.** When a gland divides, it dies instead with probability
   $P_\alpha = \alpha / F$, with baseline $\alpha = 0.2$; otherwise it splits into two glands that
   occupy neighbouring space on the lattice. Fitness acts only through survival, so fitter glands die less often.
2. **Alterations.** At each division a new somatic alteration (copy-number change or point mutation)
   occurs with probability $\mu$ per gland per division, and is inherited by all descendants.
3. **Fitness changes.** Each new alteration shifts the gland's fitness by an independent increment
   $\Delta \sim \mathcal{N}(0, \sigma^2)$, with fitness kept in the range $1 \le F \le 5$. All cells of
   a gland share its fitness.

For $\sigma = 0$ every clone has the same fitness, and the model is neutral growth. For $\sigma > 0$
new alterations can be advantageous or deleterious, and $\sigma$ sets how strong selection between
subclones can be. At the end, glands are sampled from the simulated tumour exactly as in the
experiment (5 glands from each of two opposite sides), keeping each alteration's pattern of presence
across the sampled glands.

## Remarks

The model formalizes the Big Bang picture: the tumour grows as one expansion in which many
subclones arise early and intermix, rather than by successive clonal sweeps. Early alterations are
copied into an exponentially growing population, so an alteration that arises when the tumour has a
few thousand glands ends up in a large, spatially scattered fraction of the final mass while staying
subclonal ("variegated"). Alterations that arise late stay confined to small regions or single glands.
In a tumour of billions of cells, even moderate fitness differences acting after the first few
divisions barely change the clonal composition. When the model was fitted to colorectal carcinomas,
fitness effects were detectable but had limited effect, and most public and private alterations were
dated to when the neoplasm had fewer than $10^4$ to $10^5$ cells.

## Sources

- A. Sottoriva, H. Kang, Z. Ma, T. A. Graham, M. P. Salomon, J. Zhao, P. Marjoram, K. Siegmund,
  M. F. Press, D. Shibata, C. Curtis, "A Big Bang model of human colorectal tumor growth", Nature
  Genetics 47 (2015) 209-216, Online Methods, "Computational framework",
  <https://doi.org/10.1038/ng.3214> (PMC4575589).
