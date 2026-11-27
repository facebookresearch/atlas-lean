# Consistency of implicit causal models with a latent population-structure confounder

**Model.** A genome-wide association study has $N$ individuals, $M$ SNPs $x_n=(x_{n1},\dots,x_{nM})$ and a trait $y_n$. Population structure and cryptic relatedness act as a latent confounder $z_n$ that affects both genotypes and trait. An *implicit causal model* writes every causal mechanism as a flexible function, for example a neural network, of its parents and an independent noise variable:

$$z_n=g_z(\epsilon_{z_n}),\qquad x_{nm}=g_{x_m}(\epsilon_{x_{nm}},z_n\mid w_m),\qquad y_n=g_y(\epsilon_{y_n},x_{n,1:M},z_n\mid\theta),$$

with $\epsilon\sim s(\cdot)$ i.i.d., per-SNP parameters $w_m$ with prior $p(w_m)$, and trait parameters $\theta$ with prior $p(\theta)$. The target is the causal effect $p(y\mid\mathrm{do}(x_m),x_{-m})$, which is not identifiable from $(x,y)$ alone without modelling $z$. The trait mechanism is estimated through the posterior that averages over the inferred confounders:

$$p(\theta\mid\mathbf x,\mathbf y)=\int p(\mathbf z\mid\mathbf x,\mathbf y)\,p(\theta\mid\mathbf x,\mathbf y,\mathbf z)\,d\mathbf z .$$

**Proposition (finite-dimensional global confounder).** Consider the global-confounder model

$$\beta=f_\beta(\epsilon_\beta),\qquad x_n=f_x(\epsilon_{x,n},\beta\mid\phi),\qquad y_n=f_y(\epsilon_{y,n},x_n,\beta\mid\theta),\qquad n=1,\dots,N,$$

with one confounder $\beta\in\mathbb R^d$ shared by all individuals, $d$ fixed, jointly independent noise and finite-dimensional parameters. Assume:

1. the causal graph $\beta\to x_n$, $\beta\to y_n$, $x_n\to y_n$ is correct;
2. the model family contains the true data-generating process, at a true confounder value $\beta^*$ and true trait mechanism $f_y^*$, and the joint parametric model for $(\beta,\theta)$ satisfies the conditions of the Bernstein–von Mises theorem at the truth (identifiability, local asymptotic normality with nonsingular Fisher information, and a prior with a continuous positive density there).

Then, as $N\to\infty$ with $d$ fixed, the posterior $p(\beta\mid\mathbf x,\mathbf y)$ concentrates at $\beta^*$, and the posterior of $\theta$ concentrates on parameters whose mechanism is $f_y^*$. Since $p^*(y\mid\mathrm{do}(x),\beta^*)=p^*(y\mid x,\beta^*)$, the posterior predictive of $y$ under $\mathrm{do}(x)$ converges to the true interventional distribution. The source states its Proposition 1 for the per-individual confounders $z_n$ above, whose number grows with $N$; its proof covers only this finite-dimensional global case, and the per-individual statement is not claimed here.

**Universal approximation.** A bounded, nonconstant, increasing continuous activation $\sigma$ is not a polynomial, so by the [universal approximation theorem](../../../../../Analysis/approximation-theory/universal-approximation.md) every mechanism that is continuous on a unit cube is approximated uniformly within any $\delta>0$ by a one-hidden-layer network $\sum_{i=1}^Hv_i\sigma(w_i^\top x+b_i)$. Hence implicit causal models with the same noise distributions approximate any causal model with such mechanisms.

## Depends on

- [Universal approximation theorem](../../../../../Analysis/approximation-theory/universal-approximation.md)

## Proof depends on

- [The back-door adjustment](../../../../../ComputerScience/machine-learning/probabilistic-graphical-models/causal-bayesian-networks/backdoor-adjustment.md)

## Expansion

Once the finite-dimensional global structure $\beta$ is fixed, the back-door criterion with an empty adjustment set reduces $p(y\mid\mathrm{do}(x),\beta)$ to $p(y\mid x,\beta)$. Because $\beta$ has fixed dimension while $N\to\infty$, the Bernstein–von Mises theorem applies and the posterior of $\beta$ concentrates at $\beta^*$. Conditionally on that, the posterior of $\theta$ concentrates on the true mechanism. This gives formal backing to the usual two-stage GWAS heuristic of first learning population structure (principal components or a kinship model) and then adjusting the association test for it. The argument is a well-specification result, so it does not cover a misspecified confounder model, a finite sample, or per-individual confounders $z_n$, where the number of latent variables grows with $N$ and Bernstein–von Mises does not apply as stated. In practice the posterior is approximated by likelihood-free variational inference.

## Sources

- Dustin Tran, David M. Blei, "Implicit Causal Models for Genome-wide Association Studies", International Conference on Learning Representations (ICLR 2018), <https://openreview.net/forum?id=SyELrEeAb>; preprint arXiv:1710.10742 (2017), sections "Implicit Causal Models" (universal approximation theorem) and "Implicit Causal Models with Latent Confounders" (GWAS model and Proposition 1), Section 2.1 (global-confounder model (1)) and Appendix A (consistency proof, for a global confounder with finite dimension), <https://doi.org/10.48550/arXiv.1710.10742>.
