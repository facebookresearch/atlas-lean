# Final-size dichotomy for SIR on the stochastic block model

**Setting.** Consider the SIR epidemic of rate $\beta$ (transmission per edge) and $\gamma$ (recovery) on $G \sim \mathrm{SBM}(V,W)$ with $W$ irreducible, started from $o(n)$ infected vertices and susceptible densities $\frac1n S_k(0) \to s_k(0) > 0$. Define the forward and backward offspring matrices

$$M = W \operatorname{diag}(\vec s(0)), \qquad M^{\mathrm{SIR}} = \frac{\beta}{\beta+\gamma}\, W \operatorname{diag}(\vec s(0)),$$

the basic reproduction number $R_0 = \lambda_{\max}(M^{\mathrm{SIR}})$, the survival probability $\pi_k$ of the epidemic run on a multi-type Poisson branching process with offspring matrix $M$ started from type $k$, and the survival probability $\theta_k$ of the multi-type Poisson Galton–Watson process with mean matrix $M^{\mathrm{SIR}}$ started from type $k$ (the *backward* branching process). Then $\pi_k > 0$ iff $R_0 > 1$.

**Theorem.** Assume $\frac1n \vec I(0) \to 0$ and $1 - \prod_k (1-\pi_k)^{I_k(0)} \to \pi \in [0,1]$ in probability. Then the vector of final outbreak fractions $\frac1n\big(\vec I(0) + \vec S(0) - \vec S(\infty)\big)$ converges in probability to a random vector equal to $\operatorname{diag}(\vec\theta)\, \vec s(0)$ with probability $\pi$ and to $0$ with probability $1-\pi$.

**Corollary (single initial case of label $k$).** Let $N_n \to \infty$ with $N_n/n \to 0$. Then
1. $\mathbb{P}(S(0) - S(\infty) > N_n) \to \pi_k$;
2. if $R_0 \le 1$, the final size converges in distribution to the total size of the local infection tree, with exponentially decaying tails when $R_0 < 1$;
3. if $R_0 > 1$, conditioned on being at most $N_n$, the final size has exponentially decaying tails;
4. if $R_0 > 1$, conditioned on exceeding $N_n$, $\frac1n(\vec S(0) - \vec S(\infty)) \to \operatorname{diag}(\vec\theta)\, \vec s(0)$ in probability.

So outbreaks are either $O(1)$ or of order $n$, and a vertex of label $k$ is eventually infected in a large outbreak with probability $\theta_k$.

## Depends on

- [Law of large numbers for SIR on the sparse stochastic block model](law-of-large-numbers-for-sir-on-the-stochastic-block-model.md)

## Expansion

Locally the SBM is a multi-type Poisson tree, so the early epidemic couples with a branching process until it reaches size $N_n$; this gives the probability $\pi$ of a large outbreak. Once a large outbreak has started, the uniform-in-time law of large numbers pins its final size to the ODE limit, and solving the final-size equations for the limit shows that the fraction of label-$k$ vertices infected equals the survival probability of the branching process that traces potential infectors *backwards* from a vertex: each vertex is reached through an edge that transmits before its source recovers, which has probability $\beta/(\beta+\gamma)$.

## Sources

- Christian Borgs, Karissa Huang, Christian Ikeokwu, "A Law of Large Numbers for SIR on the Stochastic Block Model: A Proof via Herd Immunity", arXiv:2410.07097 (2024), Section 2 ("Notation and Statements of Results"), single-vertex final-size theorem and its corollary; Section 5, <https://doi.org/10.48550/arXiv.2410.07097>.
