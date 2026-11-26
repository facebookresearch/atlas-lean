# Complete-data likelihood of an SEIR epidemic on a status-dependent dynamic network

Let $X_i(t)\in\{S,E,I,R\}$ be the disease state of individual $i\in\{1,\dots,N\}$ and $A_{ij}(t)\in\{0,1\}$ the state of the contact edge between $i$ and $j$. The joint latent state $Z(t)=(X(t),A(t))$ is a continuous-time Markov chain on a finite state space with intensities
$$
\lambda_i^{SE}=\beta I_i(Z)+\xi,\qquad \lambda_i^{EI}=\kappa,\qquad \lambda_i^{IR}=\gamma,\qquad I_i(Z)=\sum_{j\ne i}A_{ij}\mathbf 1\{X_j=I\}.
$$
Here $\beta$ is the within-network transmission rate and $\xi\ge0$ the external infection pressure. Edges between individuals in states $(a,b)$ form at rate $\eta_{ab}$ and dissolve at rate $\tau_{ab}$ (symmetric in $a,b$). Symptoms $Y$ and reported contacts $B$ are observed at discrete times, with kernels that are conditionally independent given the latent path (for example sensitivity $s$ and specificity $c$ for reported contacts).

With ordered latent event times $\tau_1<\dots<\tau_K\le T$ and total exit rate $\Lambda_\theta(z)$, the complete-data likelihood factorizes as
$$
L(\theta;Z_{[0,T]},Y,B)=\prod_{k=1}^Kq_\theta\big(Z(\tau_k^-),Z(\tau_k)\big)\exp\Big\{-\int_0^T\Lambda_\theta(Z(u))\,du\Big\}\cdot p_\theta(Y,B\mid Z_{[0,T]}).
$$
The epidemic block of the log-likelihood is
$$
N^{\rm int}_{SE}\log\beta-\beta U_{SI}+N^{\rm ext}_{SE}\log\xi-\xi U_S+N_{EI}\log\kappa-\kappa U_E+N_{IR}\log\gamma-\gamma U_I,
$$
where the $N$'s count internal and external infections, onsets and removals, $U_{SI}=\int_0^TS_I(u)\,du$ is the integrated susceptible–infectious contact exposure, and $U_S,U_E,U_I$ are the integrated compartment sizes. The complete-data maximum likelihood estimators therefore take occurrence/exposure form:
$$
\hat\beta=\frac{N^{\rm int}_{SE}}{U_{SI}},\qquad\hat\xi=\frac{N^{\rm ext}_{SE}}{U_S},\qquad\hat\kappa=\frac{N_{EI}}{U_E},\qquad\hat\gamma=\frac{N_{IR}}{U_I},
$$
and the network rates are estimated the same way, from formation and dissolution counts over dyad exposure. Under standard counting-process regularity, $\sqrt n(\hat\theta-\theta_0)\to N(0,\mathcal I(\theta_0)^{-1})$. The observed-data likelihood, which integrates over latent paths, is intractable for moderate $N$, so inference augments latent event times, states and unobserved edges, and alternates path and parameter updates.

## Expansion

The path density of a finite-state Markov jump process is the product of the jump intensities times the survival factor $\exp(-\int\Lambda)$. Because each rate is linear in one parameter, the log-likelihood separates into independent Poisson-type terms $N\log\theta-\theta U$, each maximized at $N/U$. The second derivative $-N/\theta^2<0$ confirms a maximum whenever the count is positive.

## Sources

- M. Asaduzzaman, "A Complete-Data Likelihood for Epidemic Processes on Partially Observed Dynamic Networks", arXiv:2607.15179 (2026), Sections 3–5 (intensities, Propositions 1–3, Theorem 1 with its epidemic-parameter derivation, Theorem 2). <https://doi.org/10.48550/arXiv.2607.15179>
