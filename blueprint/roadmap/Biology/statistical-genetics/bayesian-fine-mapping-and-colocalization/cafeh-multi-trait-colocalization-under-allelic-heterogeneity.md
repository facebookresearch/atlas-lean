# CAFEH: joint fine-mapping and colocalization across many traits under allelic heterogeneity

Let $Y \in \mathbb{R}^{N \times T}$ hold $T$ traits (e.g. expression of one gene in $T$ tissues) for $N$ individuals and $X \in \mathbb{R}^{N \times G}$ their genotypes at $G$ variants in a locus. **CAFEH** (colocalization and fine-mapping in the presence of allelic heterogeneity) assumes the additive models $Y_{it} = X_i^\top b_t + \epsilon_{it}$, $\epsilon_{it} \sim \mathcal{N}(0, \tau_t^{-1})$ i.i.d., with effects built from $K$ shared single-variant components:

$$b_t = \sum_{k=1}^{K} \varphi_k\, s_{tk}\, w_{tk}, \qquad \varphi_k \sim \mathrm{Categorical}(\pi_0), \quad s_{tk} \sim \mathrm{Bernoulli}(p_{0k}), \quad w_{tk} \sim \mathcal{N}(0, \alpha_{tk}^{-1}),$$

with $\alpha_{tk} \sim \mathrm{Gamma}(a_0, b_0)$ and $\tau_t \sim \mathrm{Gamma}(c_0, d_0)$. Here $\varphi_k \in \{0,1\}^G$ is a one-hot vector selecting the causal variant of component $k$ (shared by all traits), $\pi_0$ is the prior over variants, and $s_{tk}$ switches component $k$ on or off in trait $t$, with a trait- and component-specific effect $w_{tk}$.

- **Fine-mapping** is inference on $\varphi_1, \dots, \varphi_K$: the posterior of $\varphi_k$ concentrates on a group of linked variants carrying one association signal.
- **Colocalization** is read off the activity indicators: traits $t_1, t_2$ **colocalize in component $k$** if $s_{t_1 k} = s_{t_2 k} = 1$; they colocalize in some component if this holds for at least one $k$.
- At most $K$ variants have nonzero effect in each trait. For $T = 1$ the model is the Sum of Single Effects (SuSiE) model with a spike-and-slab prior on each single effect.

**Summary-statistic version (CAFEH-S).** With marginal estimates $\hat\beta_t$, standard errors $\hat\sigma_t$, LD matrix $\hat R$ and $\hat S = \operatorname{diag}(s_i)$, $s_i^2 = \hat\beta_{ti}^2/N + \hat\sigma_{ti}^2$, the likelihood of $Y_t$ given $b_t$ is, up to a constant, that of the RSS model

$$\hat\beta_t \sim \mathcal{N}\big(\hat S \hat R \hat S^{-1} b_t,\ \hat S \hat R \hat S\big).$$

The posterior is approximated by coordinate-ascent variational inference over the factorized family $\prod_{t,k} q(w_{tk} \mid \varphi_k, s_{tk})\, q(s_{tk})\, q(\alpha_{tk}) \prod_k q(\varphi_k) \prod_t q(\tau_t)$, all of whose updates are in closed form.

## Depends on

- [The five colocalization hypotheses](coloc-hypothesis.md)

## Expansion

Pairwise colocalization methods such as coloc enumerate configurations under at most one causal variant per trait, so loci with several distinct causal variants in high LD can be mislabelled as shared, or as distinct, depending on which variant leads in each trait. Meta-analysis-based sharing calls (e.g. Metasoft) inflate sharing further, because they compare effect estimates at one variant regardless of whether the same causal signal drives them. CAFEH separates the question "which variants are causal" (shared $\varphi_k$) from "which traits each causal variant acts on" (per-trait $s_{tk}$), so allelic heterogeneity is a set of components, each colocalizing in its own subset of traits. Giving every effect its own precision $\alpha_{tk}$ lets effect magnitudes vary freely across traits and components. Pooling traits sharpens the posterior on $\varphi_k$, which improves fine-mapping power for shared variants. Re-analysis of 49 GTEx tissues with this model finds cis-eQTL effects to be largely tissue specific once LD and multiple signals are modelled.

## Sources

- M. Arvanitis, K. Tayeb, B. J. Strober and A. Battle, "Redefining tissue specificity of genetic regulation of gene expression in the presence of allelic heterogeneity", The American Journal of Human Genetics 109 (2022), 223–239, Material and methods ("CAFEH", "Fitting CAFEH from summary statistics", "Variational inference for CAFEH"), <https://doi.org/10.1016/j.ajhg.2022.01.002> (PMC8874223).
- X. Zhu and M. Stephens, "Bayesian large-scale multiple regression with summary statistics from genome-wide association studies", Annals of Applied Statistics 11 (2017), 1561–1592, Proposition 2.1.
