# Moments and Fano factors of the three-stage gene expression model

In the classical three-stage model of protein production, a gene switches between an inactive state $I=0$ and an active state $I=1$ at rates $k_+$ ($0\to1$) and $k_-$ ($1\to0$); while active it produces mRNAs at rate $k_M$; each mRNA lives an $\mathrm{Exp}(\gamma_M)$ time and produces proteins at rate $k_P$; each protein lives an $\mathrm{Exp}(\gamma_P)$ time. The process $(I(t), M(t), P(t))$ is an irreducible Markov process on $\{0,1\}\times\mathbb{N}^2$ with a unique invariant law, which has finite second moments. If $(I,M,P)$ has this law, $\delta_+ = k_+/(k_+ + k_-)$ and $\Lambda = k_+ + k_-$, then

$$\mathbb{E}(I) = \delta_+, \qquad \mathbb{E}(M) = \delta_+ \frac{k_M}{\gamma_M}, \qquad \mathbb{E}(P) = \delta_+ \frac{k_M k_P}{\gamma_M \gamma_P},$$

$$\frac{\mathrm{Var}(M)}{\mathbb{E}(M)} = 1 + (1-\delta_+)\frac{k_M}{\Lambda + \gamma_M},$$

$$\frac{\mathrm{Var}(P)}{\mathbb{E}(P)} = 1 + \frac{k_P}{\gamma_M + \gamma_P} + (1-\delta_+)\frac{k_M k_P}{\gamma_M + \gamma_P}\cdot\frac{\Lambda + \gamma_M + \gamma_P}{(\Lambda + \gamma_M)(\Lambda + \gamma_P)} .$$

In particular the protein Fano factor always exceeds $1$, while for a constitutively active gene ($k_- = 0$) the mRNA number is Poisson.

## Expansion

At equilibrium $\mathbb{E}[Q f(I,M,P)] = 0$ for the generator $Q$ and polynomial test functions. The choices $f = i, x, y$ give the three means; $f = x^2, y^2, xy, ix, iy$ give a closed linear system for $\mathbb{E}(M^2), \mathbb{E}(P^2), \mathbb{E}(MP), \mathbb{E}(IM), \mathbb{E}(IP)$, whose solution yields the variances. The excess over $1$ splits into a translational-burst term $k_P/(\gamma_M+\gamma_P)$ and a promoter-switching term proportional to $1-\delta_+$.

## Sources

- Philippe Robert, "Mathematical models of gene expression", Probability Surveys 16 (2019), 277–332, <https://doi.org/10.1214/19-ps332>; numbering as in arXiv:1905.02578: Section 2 (Propositions 2, 4 and 5) and the central limit theorem of Section 6.
