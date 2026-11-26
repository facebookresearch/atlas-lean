# Low-frequency approximation of microbiome exchange as a basin Markov chain

**Model.** Hosts $h^{(1)},\dots,h^{(|H|)}$ sit on a weighted network with interaction-frequency parameters $\lambda_{ij}\ge0$; write $\lambda_{\rm tot}=\sum_{i<j}\lambda_{ij}$ and $l_{ij}=\lambda_{ij}/\lambda_{\rm tot}$. Host $i$ carries a microbiome abundance vector $N^{(i)}(t)\in[0,M]^n$. Between interactions, $\dot N^{(i)}=g^{(i)}(N^{(i)})$, where each local-dynamics function $g^{(i)}$ keeps $[0,M]^n$ invariant. Each pair $(i,j)$ interacts at the event times of an independent Poisson process of rate $\lambda_{ij}$, and at an interaction time $t_I$ the two hosts exchange a fraction $\gamma\in(0,1]$ of their microbiomes:
$$N^{(i)}(t_I^+)=(1-\gamma)N^{(i)}(t_I^-)+\gamma N^{(j)}(t_I^-),\qquad N^{(j)}(t_I^+)=(1-\gamma)N^{(j)}(t_I^-)+\gamma N^{(i)}(t_I^-).$$
The result is a piecewise-deterministic Markov process.

**Basin description.** Suppose the attractors of each $g^{(i)}$ are finitely many stable equilibria, labelled $1,\dots,m_i$, at which $g^{(i)}$ points inward. Let $\Psi_{b_1\dots b_{|H|}}(t)$ be the probability that host $k$ is in basin $b_k$ for every $k$ (the basin probability tensor). For $\gamma$ outside the set $\mathcal B$ of strengths that can send a post-exchange state onto a basin boundary, an exchange between hosts $i,j$ sitting at equilibria in basins $a_i,a_j$ lands them in determined basins $b_i,b_j$; this defines a 0-1 pairwise interaction operator $\Phi^{(ij)}$ on basin configurations, and the total interaction operator is $\Phi=\sum_{i<j}l_{ij}\Phi^{(ij)}$.

**Theorem (LFA).** Fix $\gamma\notin\mathcal B$, all $l_{ij}$, and a horizon $T^*$ in frequency-scaled time $t^*=\lambda_{\rm tot}t$. As $\lambda_{\rm tot}\to0$, $\Psi(t^*)$ converges uniformly on $[0,T^*]$ to the solution $\widetilde\Psi$ of the linear master equation
$$\frac{d\widetilde\Psi_{b}}{dt^*}=\Phi_{b,a}\widetilde\Psi_{a}-\widetilde\Psi_{b},\qquad \widetilde\Psi(0)=\Psi(0)$$
(summation over the repeated multi-index $a$).

## Expansion

When interactions are rare relative to the local relaxation time, every host has relaxed to an equilibrium before its next interaction, so only basin labels matter. Interactions occur at total rate $\lambda_{\rm tot}$ and pick the pair $(i,j)$ with probability $l_{ij}$; each one maps basin configurations deterministically through $\Phi^{(ij)}$. In the rescaled time the basin process is therefore a continuous-time Markov chain with generator $\Phi-I$, and the error from interactions that arrive before relaxation vanishes as $\lambda_{\rm tot}\to0$. This extends patch-occupancy metacommunity models (Levins type) to discrete, pairwise host contacts, with the colonization rules derived from the local dynamics rather than postulated.

## Sources

- Michael Johnson, Mason A. Porter, "Interacting Hosts with Microbiome Exchange: An Extension of Metacommunity Theory for Discrete Interactions between Hosts", arXiv:2507.11958 (2025), Theorem 3.1 (Section 3; proof in Appendix A), <https://doi.org/10.48550/arXiv.2507.11958>
