# Constant relative mutability test for recent gene acquisition

**Setting.** Sites evolve i.i.d. under a substitution model with a distance correction $d = \mathrm{corr}(h)$ from normalized Hamming distance $h$ to expected substitutions per site (e.g. Jukes–Cantor) and inverse $h = \mathrm{corr}^{-1}(d)$. Genes $g, g'$ have **constant relative mutability** (CRM) if their substitution rates keep a constant ratio $\rho = r_g/r_{g'}$ at all times (the universal-pacemaker approximation).

**Observation.** Under CRM, the expected distance for $g'$ between two sequences is $\delta_{g'} = \mathrm{corr}(h_g)/\rho$.

**Lemma.** If $h_{g'} = \mathrm{corr}^{-1}(\delta_{g'})$ is the expected Hamming distance and $\hat h_{g'}$ the observed one over $n$ sites, then

$$\Pr\big(|h_{g'} - \hat h_{g'}| > \varepsilon\big) \le 2e^{-2n\varepsilon^2}.$$

**Theorem.** Let $g$ (length $n$) be suspected of transfer between strains $S_1, S_2$; let $w$ be a witness gene present in $S_1, S_2$ and in two reference organisms $R_1, R_2$ that also carry $g$. With the expected Hamming distances $h_g(R), h_w(R), h_w(S)$ between the references and between the strains, set

$$\delta_g(S) = \frac{\mathrm{corr}(h_g(R))}{\mathrm{corr}(h_w(R))}\,\mathrm{corr}(h_w(S)).$$

Under vertical inheritance with CRM, the observed distance $\hat h_g(S)$ of $g$ between the strains satisfies

$$\Pr\big(|\hat h_g(S) - \mathrm{corr}^{-1}(\delta_g(S))| > \varepsilon\big) \le 2e^{-2n\varepsilon^2}.$$

The practical test replaces $h_g(R), h_w(R), h_w(S)$ by the observed $\hat h_g(R), \hat h_w(R), \hat h_w(S)$, giving the plug-in value $d_g(S)$, and rejects vertical descent of $g$ at level $\delta_r$ when $|\hat h_g(S) - \mathrm{corr}^{-1}(d_g(S))| > \sqrt{\ln(2/\delta_r)/(2n)}$. This plug-in test is an approximation: the bound above does not account for the estimation error of the three plug-in distances, which the test ignores.

## Proof depends on

- [Two-sided Hoeffding inequality for averages of bounded variables](../../../../Probability/concentration-inequalities/hoeffding-s-inequality/measure-real-abs-avg-sub-ge-le.md)

## Expansion

Expected substitutions equal rate times elapsed time, so CRM transfers a distance from one gene to another by dividing by $\rho$; the ratio is estimated on the reference pair, where $g$ is assumed vertical. Distances are compared in Hamming space because the observed Hamming distance is a mean of $n$ independent site indicators, to which Hoeffding's inequality applies directly. A gene recently acquired by transfer is markedly less diverged between the strains than the witness predicts, whereas a translocated gene has accumulated the full expected divergence; combining this with a significantly low synteny index separates transfer from rearrangement.

## Sources

- G. Sevillya, O. Adato, S. Snir, "Detecting horizontal gene transfer: a probabilistic approach", BMC Genomics 21(Suppl 1) (2020) 106, Definition 1, Observation 3 (Eqs (7)–(8)), Lemma 2 (Eqs (9)–(10)), Theorem 1 (Eq (11)) and Corollary 3, <https://doi.org/10.1186/s12864-019-6395-5>, PMCID PMC7057450.
