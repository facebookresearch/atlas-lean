# Limit theorem for stationary distributions of Langmuir birth–death processes

Let $X_N^{(i)}$ be the stationary distribution of the [Langmuir birth–death process](langmuir-birth-death-process-and-lig-distribution.md) $M_i$ on $\{0,\dots,N\}$, $i=1,2,3$, with rate constants $c_1,c_2,c_3>0$, and set

$$
a=\frac{c_1}{c_3},\qquad b=\frac{c_1+c_2}{c_3},\qquad Y_N^{(i)}=\frac{X_N^{(i)}}{N}.
$$

**Theorem.** As $N\to\infty$, $Y_N^{(i)}\to\mathcal Z_i$ in distribution, where

1. $\mathcal Z_1\sim LIG(a,b)$;
2. $1-\mathcal Z_2\sim LIG(b-a,b)$;
3. $\mathcal Z_3\sim\mathrm{Beta}(a,\,b-a)$.

In every case the limiting mean is the Langmuir steady state $c_1/(c_1+c_2)=a/b$.

## Expansion

For a birth–death process on a finite state space the stationary law is explicit from detailed balance, $\pi(k+1)/\pi(k)=b(k)/d(k+1)$. For polynomial rates of the given density-dependent form these ratios produce, after rescaling, products of Gamma-function ratios, and the proof shows that the moments of $Y_N^{(i)}$ satisfy in the limit the same recursions as the claimed limits; since the limits live on $[0,1]$ they are determined by their moments. A key analytic step is the asymptotic $N^{-\alpha_N}\sum_{k=0}^N\frac{\Gamma(\alpha_N+k)}{k!}(1-\beta_N/N)^k\to\beta^{-\alpha}\Gamma(\alpha,\beta)$ for $\alpha_N\downarrow\alpha$ with $(\alpha_N-\alpha)\log N\to0$ and $\beta_N\to\beta$. Model $M_1$ yields saturation (an atom at full occupancy), $M_2$ a threshold effect (an atom at an empty probe), and the boundary-smooth $M_3$ a Beta law with no atoms; this distinguishes the discrete-equilibrium limit from the gamma stationary law of the diffusion approximation.

## Depends on

- [Langmuir birth–death process of probe hybridization and the Langmuir-incomplete gamma law](langmuir-birth-death-process-and-lig-distribution.md)

## Proof depends on

- [Stationary law of a finite birth–death chain](../../../../Probability/markov-chains/birth-death-processes/stationary-law-of-a-finite-birth-death-chain.md)

## Sources

- Grzegorz A. Rempala, Iwona Pawlikowska. *Limit Theorems for Hybridization Reactions on Oligonucleotide Microarrays* (2008), Sections 2–3: Definitions 2.1 and 3.1, Theorem 1 and Lemmas 1–2. <https://doi.org/10.48550/arXiv.0802.1192>
