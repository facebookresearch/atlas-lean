# Equilibrium moments of gene expression with transcription and translation delays

**Model.** A gene switches between inactive and active states at rates $\lambda_1^+$ (on) and $\lambda_1^-$ (off); set $\tau_1=1/(\lambda_1^++\lambda_1^-)$. An active gene produces RNA at rate $\lambda_2$. Each transcript becomes available only after an independent random delay $G_2\sim\mu$, and it degrades at rate $1/\tau_2$. Each available transcript initiates translation at rate $\lambda_3$. Each protein becomes available after an independent delay $G_3\sim\nu$ and degrades at rate $1/\tau_3$:

$$\text{inactive}\ \underset{\lambda_1^-}{\overset{\lambda_1^+}{\rightleftharpoons}}\ \text{active},\qquad \text{active}(t)\xrightarrow{\lambda_2}\text{active}(t)+\text{RNA}(t+G_2),\qquad \text{RNA}(t)\xrightarrow{\lambda_3}\text{RNA}(t)+\text{protein}(t+G_3).$$

Let $\mathcal N_1,\mathcal N_2,\mathcal N_3$ be the numbers of active genes (per gene copy), available RNA and available protein. Let $G_2,G_2'\sim\mu$ and $G_3,G_3'\sim\nu$ be independent.

**Theorem.** In equilibrium:

1. $\mathbf E[\mathcal N_1]=\lambda_1^+\tau_1$, $\mathbf{Var}[\mathcal N_1]=\lambda_1^+\lambda_1^-\tau_1^2$, and $\mathbf{Cov}[\mathcal N_1(0),\mathcal N_1(t)]=\lambda_1^+\lambda_1^-\tau_1^2e^{-|t|/\tau_1}$.
2. $\mathbf E[\mathcal N_2]=\lambda_1^+\lambda_2\tau_1\tau_2$ and

$$\mathbf{Var}[\mathcal N_2]=\lambda_1^+\lambda_2\tau_1\tau_2+\lambda_1^+\lambda_1^-\lambda_2^2\tau_1^2\tau_2^2\,\frac{\tau_1}{\tau_1+\tau_2}\,\frac{\tau_1\mathbf E\big[e^{-|G_2-G_2'|/\tau_1}\big]-\tau_2\mathbf E\big[e^{-|G_2-G_2'|/\tau_2}\big]}{\tau_1-\tau_2}.$$

3. $\mathbf E[\mathcal N_3]=\lambda_1^+\lambda_2\lambda_3\tau_1\tau_2\tau_3$ and

$$\mathbf{Var}[\mathcal N_3]=\lambda_1^+\lambda_2\lambda_3\tau_1\tau_2\tau_3+\lambda_1^+\lambda_2\lambda_3^2\tau_1\tau_2\tau_3^2\,A+\lambda_1^+\lambda_1^-\lambda_2^2\lambda_3^2\tau_1^2\tau_2^2\tau_3^2\,B,$$

with

$$A=\frac{\tau_2}{\tau_2+\tau_3}\,\frac{\tau_2\mathbf E\big[e^{-|G_3-G_3'|/\tau_2}\big]-\tau_3\mathbf E\big[e^{-|G_3-G_3'|/\tau_3}\big]}{\tau_2-\tau_3}.$$

$B$ is the analogous combination of $\mathbf E\big[e^{-|G_3-G_3'+G_2-G_2'|/\tau_j}\big]$, $j=1,2,3$.

Means do not depend on the delays. Delays enter the variances only through the Laplace-type quantities $\mathbf E[e^{-|D-D'|/\tau}]$ of the difference of two independent delays. These quantities equal $1$ for deterministic delays and are smaller otherwise. In particular $\mathbf{Var}[\mathcal N_2]\le\lambda_1^+\lambda_2\tau_1\tau_2+\lambda_1^+\lambda_1^-\lambda_2^2\tau_1^2\tau_2^2\frac{\tau_1}{\tau_1+\tau_2}$, the delay-free value, with equality iff $\mu$ is a point mass: random transcription delays strictly reduce equilibrium RNA noise. For exponential delays with means $\sigma_2,\sigma_3$, $\mathbf E[e^{-|G_2-G_2'|/\tau}]=\tau/(\sigma_2+\tau)$.

## Proof sketch

The model is a cascade of linear birth–death processes driven by a Markov telegraph signal, so equilibrium moments follow from Campbell-type formulas for marked Poisson processes. A transcript created at time $s$ is present at $t$ iff $s+G_2\le t$ and it survives an $\mathrm{Exp}(1/\tau_2)$ lifetime started at creation. Covariances between two transcripts created at different times therefore involve $|G_2-G_2'|$ smoothed against the exponential kernels of the gene switch and of RNA decay. The key identity, for $T,T'$ i.i.d. exponential with mean $\sigma$,

$$\mathbf E\big[e^{-|t+T+G-T'-G'|/\tau}\big]=\frac{\tau}{\tau+\sigma}\cdot\frac{\tau\mathbf E[e^{-|G'-G-t|/\tau}]-\sigma\mathbf E[e^{-|G'-G-t|/\sigma}]}{\tau-\sigma},$$

propagates these terms through each stage. With all delays set to zero the formulas reduce to the classical three-stage (telegraph–RNA–protein) noise decomposition. The inequality comes from convexity of $t\mapsto\mathbf E[e^{-St}]$ for $S\ge0$. Writing $1=\frac{\tau_1}{\tau_1-\tau_2}-\frac{\tau_2}{\tau_1-\tau_2}$ gives $\frac{\tau_1\mathbf E[e^{-S/\tau_1}]-\tau_2\mathbf E[e^{-S/\tau_2}]}{\tau_1-\tau_2}\le1$, with equality iff $S$ is almost surely constant.

## Sources

- Martin Jansen and Peter Pfaffelhuber, "Stochastic gene expression with delay", *Journal of Theoretical Biology* 364 (2015), 355–363, <https://doi.org/10.1016/j.jtbi.2014.09.031>. Preprint version: arXiv:1305.6635v2 (2014), Section 2 (model), Proposition 3.1 (gene state), Theorem 3.2 (RNA moments), Theorem 3.4 (protein moments with $A,B$), Lemmas 4.1–4.2 and Corollary 4.3 (uniform, exponential and nearly deterministic delays), Lemma A.1 (key lemma), <https://doi.org/10.48550/arXiv.1305.6635>.
