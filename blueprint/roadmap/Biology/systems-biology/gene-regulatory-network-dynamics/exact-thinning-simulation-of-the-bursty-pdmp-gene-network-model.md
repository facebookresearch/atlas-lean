# Exact thinning simulation of the bursty PDMP gene network model

**Model.** For $n$ genes, the two-state promoter model $G_i\rightleftharpoons G_i^*$ (rates $k_{\mathrm{on},i},k_{\mathrm{off},i}$), transcription $G_i^*\to G_i^*+M_i$ (rate $s_{0,i}$), translation $M_i\to M_i+P_i$ ($s_{1,i}$) and degradation of mRNA ($d_{0,i}$) and protein ($d_{1,i}$), taken in the bursty regime $k_{\mathrm{off},i}\gg k_{\mathrm{on},i}$ with continuous molecule levels, becomes a piecewise-deterministic Markov process (PDMP) $(Y,Z)\in\mathbb R^n_+\times\mathbb R^n_+$ of mRNA and protein levels. Between bursts,

$$Y_i'=-d_{0,i}Y_i,\qquad Z_i'=s_{1,i}Y_i-d_{1,i}Z_i,$$

and gene $i$ fires a burst at rate $k_{\mathrm{on},i}(Z)$, a bounded continuous function of all protein levels (this is how genes interact), adding an $\mathrm{Exp}(b_i)$ amount of mRNA, $b_i=k_{\mathrm{off},i}/s_{0,i}$. The generator acting on smooth $f$ is

$$Lf(y,z)=\sum_{i=1}^n\Big[-d_{0,i}y_i\,\partial_{y_i}f+(s_{1,i}y_i-d_{1,i}z_i)\,\partial_{z_i}f+k_{\mathrm{on},i}(z)\int_0^\infty\big(f(y+he_i,z)-f(y,z)\big)b_ie^{-b_ih}\,dh\Big].$$

The deterministic flow is explicit: $y_i(t)=e^{-d_{0,i}t}y_i$, $z_i(t)=e^{-d_{1,i}t}z_i+(e^{-d_{1,i}t}-e^{-d_{0,i}t})\frac{s_{1,i}}{d_{0,i}-d_{1,i}}y_i$ for $d_{0,i}\ne d_{1,i}$. Without interactions the stationary mRNA level of each gene is gamma distributed.

**Algorithm (thinning).** Fix $\lambda\ge\sup_z\sum_ik_{\mathrm{on},i}(z)$. Repeatedly draw a candidate waiting time $\tau\sim\mathrm{Exp}(\lambda)$, move along the explicit flow for time $\tau$, then accept a burst of gene $i$ with probability $k_{\mathrm{on},i}(Z)/\lambda$ (drawing its size from $\mathrm{Exp}(b_i)$) or reject with probability $1-\sum_ik_{\mathrm{on},i}(Z)/\lambda$. No numerical integration of the inhomogeneous jump hazard $\exp\!\big(-\int_0^t\sum_ik_{\mathrm{on},i}(Z(\tau))\,d\tau\big)$ is needed.

**Theorem.** The process produced by the algorithm induces a strongly continuous semigroup on bounded continuous functions whose infinitesimal generator is $L$. Hence the algorithm samples exact trajectories of the bursty PDMP model.

## Expansion

Thinning (uniformization) works because the total burst intensity is bounded by $\lambda$: a homogeneous Poisson clock of rate $\lambda$ proposes candidate times, and accepting each with probability proportional to the current intensity reproduces the time-inhomogeneous jump hazard, exactly as in Lewis-Shedler thinning of Poisson processes. To prove exactness one computes, for the embedded Markov chain sampled at candidate times, $\frac{d}{dt}\big|_{t=0}\mathbb E_{(y,z)}f(Y_t,Z_t)$: the flow part comes from following the ODE, the accepted candidates contribute the burst integral weighted by $k_{\mathrm{on},i}(z)$, and the rejected candidates cancel. Strong continuity follows from boundedness of the rates and continuity of the flow. Boundedness of $k_{\mathrm{on},i}$ is biologically natural (burst frequencies saturate), and the explicit flow makes each step cost $O(n)$, which enables simulation of large networks fitted to single-cell transcriptomic data.

## Sources

- M. Gaillard, U. Herbach, "Efficient stochastic simulation of gene regulatory networks using hybrid models of transcriptional bursting", *Lecture Notes in Computer Science* (2025), 109–125, Section 2 (reaction model and generator), Section 3 (flow, waiting-time law and thinning algorithm) and Section 5 (Theorem 1), <https://doi.org/10.1007/978-3-032-01436-8_7> (preprint arXiv:2507.01922).
