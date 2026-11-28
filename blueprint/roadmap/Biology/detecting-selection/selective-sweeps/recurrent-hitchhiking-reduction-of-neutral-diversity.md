# Recurrent hitchhiking and the protein divergence of a gene

Assume the setting of [equilibrium neutral diversity under recurrent selective sweeps](recurrent-hitchhiking-equilibrium-diversity.md), written with neutral diversity $\theta$ in place of $\pi_0$, sweep rate $\lambda$ in place of $\nu$, intensity $\gamma = 2N_es$ in place of $\alpha$ and $k$ in place of $\kappa$, so that $E(\pi) = \theta\rho/(\rho + k\gamma\lambda)$ with $k \approx 0.075$.

**Linking sweeps to protein divergence.** If a constant fraction $\alpha$ of amino acid substitutions at gene $i$ was fixed by positive selection, $K_{a,i}$ is its amino acid divergence and $T$ is the divergence time in generations to the outgroup, the local sweep rate is $\lambda_i = \alpha K_{a,i}/2T$, so

$$E(\pi_i) = \frac{\theta\rho_i}{\rho_i + k\,2N_e s\,(\alpha K_{a,i}/2T)} = \frac{\theta\rho_i}{\rho_i + \alpha s\,K_{a,i}\,(kN_e/T)},$$

with $\rho_i$ the local recombination rate. Because $N_e/T$ depends only on scaled quantities ($N_e = \theta/3\mu$ and $T = (\bar K_s - \theta)/2\mu$ for X-linked loci, so the neutral mutation rate $\mu$ cancels), $E(\pi_i)/\theta$ depends on the selection parameters only through the product $\alpha s$. Synonymous diversity therefore declines with the protein divergence of the gene, and $\alpha$ and $s$ cannot be separated from diversity data alone.

## Proof sketch

Substituting the local sweep rate $\lambda_i$ and $\gamma = 2N_es$ into the equilibrium law gives the displayed form. Fitting this relation by simulation-based maximum likelihood to 137 X-linked Drosophila coding regions estimated $\alpha s \approx 6\times10^{-6}$; combined with McDonald–Kreitman estimates of $\alpha$, adaptive amino acid substitutions are inferred to be weakly selected ($s$ of order $10^{-5}$).

## Depends on

- [Equilibrium neutral diversity under recurrent selective sweeps](recurrent-hitchhiking-equilibrium-diversity.md)

## Sources

- P. Andolfatto, "Hitchhiking effects of recurrent beneficial amino acid substitutions in the *Drosophila melanogaster* genome", Genome Research 17 (2007), 1755–1762, Methods, Equations 1–3, <https://doi.org/10.1101/gr.6691007> (PMC2099584).
