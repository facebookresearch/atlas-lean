# Spatial next-generation matrix of a mobility-coupled SEPIA network

Let $n$ communities with population sizes $N_1, \dots, N_n$ each run the
[SEPIA dynamics](sepia-compartmental-model.md), and for each state
$X \in \{S, E, P, I, A, R\}$ let $C^X = [C^X_{ij}]$ be a row-stochastic matrix
($\sum_j C^X_{ij} = 1$) whose entry $C^X_{ij}$ is the probability that an individual of community
$i$ in state $X$ makes contacts in community $j$. The force of infection in community $i$ is

$$\lambda_i = \sum_{j=1}^{n} C^S_{ij}\,
\frac{\sum_{Y \in \{P,I,A\}} \beta_Y \sum_{k=1}^{n} C^Y_{kj} Y_k}
{\sum_{X \in \{S,E,P,I,A,R\}} \sum_{k=1}^{n} C^X_{kj} X_k}.$$

Let $N = \operatorname{diag}(N_1,\dots,N_n)$, $u$ the row vector of $n$ ones,
$\Delta = \operatorname{diag}(u N C^S)$ and $G = N C^S \Delta^{-1}$. Define the generation matrices

$$G_P = \frac{\beta_P}{\delta_P}\, G\, (C^P)^{\mathsf T}, \qquad
G_I = \frac{\sigma\beta_I}{\eta + \gamma_I + \alpha_I}\, G\, (C^I)^{\mathsf T}, \qquad
G_A = \frac{(1-\sigma)\beta_A}{\gamma_A}\, G\, (C^A)^{\mathsf T}.$$

In the absence of control measures, the basic reproduction number of the network is the spectral
radius of the spatially explicit next-generation matrix

$$R_0 = \rho(K_L) = \rho(G_P + G_I + G_A).$$

The dominant eigenvalue of the Jacobian at the disease-free equilibrium gives the initial
exponential growth rate of cases, and its eigenvector gives the asymptotic geographic
distribution of infections during exponential growth.

## Depends on

- [SEPIA compartmental model](sepia-compartmental-model.md)
- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

At the disease-free equilibrium all contacts are with susceptibles, so the denominator of
$\lambda_i$ reduces to the number of susceptibles present at site $j$, $\sum_k C^S_{kj} N_k$; this
is the diagonal of $\Delta$. A case of type $Y$ resident in community $k$ spends contact time in
community $j$ with probability $C^Y_{kj}$, and the infections it causes at $j$ are spread over
residents $i$ in proportion to $N_i C^S_{ij}/\Delta_{jj}$, which is $G_{ij}$. Multiplying by the
transmission rate and the mean residence time in each infectious stage gives the three
generation matrices; the factors $\sigma$ and $1-\sigma$ are the probabilities that a presymptomatic case enters $I$ or $A$ (the main text of the source prints $G_I$ and $G_A$ without them, absorbing them into the rates). The next-generation construction then identifies $R_0$ with the spectral
radius, and the entries of $K_L$ indicate the main spatial routes of propagation.

## Sources

- M. Gatto, E. Bertuzzo, L. Mari, S. Miccoli, L. Carraro, R. Casagrandi, A. Rinaldo, "Spread and
  dynamics of the COVID-19 epidemic in Italy: Effects of emergency containment measures",
  Proceedings of the National Academy of Sciences 117 (2020) 10484-10491, Materials and Methods,
  "Epidemiological Model" (spatial force of infection and $R_0 = \rho(K_L)$), and Results,
  <https://doi.org/10.1073/pnas.2004978117> (PMC7229754).
