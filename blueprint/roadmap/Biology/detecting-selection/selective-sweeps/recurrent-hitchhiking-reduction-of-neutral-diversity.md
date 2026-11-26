# Recurrent hitchhiking reduction of neutral diversity

Let beneficial substitutions sweep to fixation near a neutral site at rate $\lambda$ per site per generation, each with selection coefficient $s$ and intensity $\gamma = 2N_es$, and let $\rho$ be the recombination rate per site per generation and $\theta$ the neutral population mutation rate. In the Wiehe–Stephan approximation the expected neutral diversity is
$$E(\pi) = \frac{\theta\rho}{\rho + k\gamma\lambda}, \qquad k \approx 0.075.$$

**Linking sweeps to protein divergence.** If a constant fraction $\alpha$ of amino acid substitutions at gene $i$ was fixed by positive selection, $K_{a,i}$ is its amino acid divergence and $T$ is the divergence time in generations to the outgroup, the local sweep rate is $\lambda_i = \alpha K_{a,i}/2T$, so
$$E(\pi_i) = \frac{\theta\rho_i}{\rho_i + k\,2N_e s\,(\alpha K_{a,i}/2T)} = \frac{\theta\rho_i}{\rho_i + \alpha s\,K_{a,i}\,(kN_e/T)},$$
with $\rho_i$ the local recombination rate. Because $N_e/T$ depends only on scaled quantities ($N_e = \theta/3\mu$ and $T = (\bar K_s - \theta)/2\mu$ for X-linked loci, so the neutral mutation rate $\mu$ cancels), $E(\pi_i)/\theta$ depends on the selection parameters only through the product $\alpha s$. Synonymous diversity therefore declines with the protein divergence of the gene, and $\alpha$ and $s$ cannot be separated from diversity data alone.

## Depends on

- [Probability that a neutral lineage stays linked during a deterministic sweep](hitchhiking-deterministic-escape-probability.md)
- [Sweep duration](sweep-duration.md)

## Expansion

Each sweep reduces diversity at a linked site by an amount that grows with $s$ and shrinks with recombination distance; integrating over sweeps occurring at rate $\lambda$ per site along the chromosome gives an effective coalescence rate inflated by a term proportional to $\gamma\lambda/\rho$, and diversity is $\theta$ divided by $1 + k\gamma\lambda/\rho$. Substituting $\lambda_i$ and $\gamma = 2N_es$ gives the second form. Fitting this relation by simulation-based maximum likelihood to 137 X-linked Drosophila coding regions estimated $\alpha s \approx 6\times10^{-6}$; combined with McDonald–Kreitman estimates of $\alpha$, adaptive amino acid substitutions are inferred to be weakly selected ($s$ of order $10^{-5}$).

## Sources

- P. Andolfatto, "Hitchhiking effects of recurrent beneficial amino acid substitutions in the *Drosophila melanogaster* genome", Genome Research 17 (2007), 1755–1762, Methods, Equations 1–3, <https://doi.org/10.1101/gr.6691007> (PMC2099584).
