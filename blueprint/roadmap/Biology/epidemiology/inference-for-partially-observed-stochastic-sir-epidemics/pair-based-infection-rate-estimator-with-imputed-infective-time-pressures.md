# Pair-based infection-rate estimator with imputed infective time pressures

**Setting.** A closed population of $N$ individuals undergoes a stochastic SIR epidemic: each infective $k$ infects each susceptible $j$ at rate $\beta/N$, and infectious periods are exponential with rate $\gamma$ (more generally Erlang with shape $m$ and rate $\gamma$). Of the $n$ ever-infected individuals, individual $j$ has infection time $i_j$ and removal time $r_j$; the first case is the index case. The *infective time pressure* exerted by $k$ on $j$ is

$$\tau_{kj}=r_k\wedge i_j-i_j\wedge i_k ,$$

the time during which $k$ was infectious while $j$ was still susceptible.

**Complete-data MLEs.** When all $(i_j,r_j)$ are observed,

$$\hat\gamma=\frac{m\,n}{\sum_{j=1}^n(r_j-i_j)},\qquad \hat\beta=\frac{(n-1)\,N}{\sum_{j=2}^n\sum_{k\ne j}\tau_{kj}+(N-n)\sum_{j=1}^n(r_j-i_j)} ,$$

the numerator counting post-index infections and the denominator the total infectious exposure of infected and never-infected individuals.

**Partial observation.** Suppose every case has at least one endpoint observed, and a calibration set $\mathcal C$ has both. Estimate $\hat\gamma=m|\mathcal C|/\sum_{j\in\mathcal C}(r_j-i_j)$ and define the pair-based estimator $\tilde\beta$ by replacing each unobservable $\tau_{kj}$ and $r_j-i_j$ in $\hat\beta$ by its conditional expectation under $\hat\gamma$ given the observed endpoints. These expectations are closed-form; e.g. with $S_\gamma(t)=e^{-\gamma t}$, $F_\gamma=1-S_\gamma$ and only removal times $r_k,r_j$ observed (exponential periods),

$$\mathbb E[\tau_{kj}]=\begin{cases}S_{\gamma_k}(r_k-r_j)\,\dfrac{\gamma_j}{\gamma_k(\gamma_k+\gamma_j)}, & r_j<r_k,\\[2mm] S_{\gamma_j}(r_j-r_k)\,\dfrac{\gamma_j}{\gamma_k(\gamma_k+\gamma_j)}+\dfrac{F_{\gamma_j}(r_j-r_k)}{\gamma_k}, & r_j>r_k,\end{cases}$$

and if $r_k,i_j$ are observed but $i_k$ is missing, $\mathbb E[\tau_{kj}]=S_{\gamma_k}(r_k-i_j)/\gamma_k$ for $i_j<r_k$ and $1/\gamma_k$ for $i_j>r_k$.

**Proposition (pathology of removal-only data).** In the homogeneous SIR model with only removal times observed, for *any* plug-in value $\gamma^\dagger$ the estimate $\tilde R_0=\tilde\beta/\gamma^\dagger$ equals exactly $2$ whenever the outbreak infects the whole population ($n=N$).

## Expansion

For the proposition: with $n=N$ the never-infected term vanishes, so $\tilde\beta=N(N-1)/\sum_{j\ge2}\sum_{k\ne j}\mathbb E_{\gamma^\dagger}[\tau_{kj}]$. The true sum $\sum_{j\ge2}\sum_{k\ne j}\tau_{kj}$ is distributed as $\sum_{j=1}^{N-1}jW_j$ with $W_j$ i.i.d. $\mathrm{Exp}(\gamma)$, and imputing from removal times alone gives $\sum_{j=1}^{N-1}j/\gamma^\dagger=N(N-1)/(2\gamma^\dagger)$, so $\tilde\beta=2\gamma^\dagger$ and $\tilde R_0=2$ regardless of the data. The imputation formulas follow by integrating the exponential (or Erlang) densities of the missing endpoints over the orderings of $i_k,i_j,r_k$; observing even a few complete infectious periods anchors $\hat\gamma$ independently of $\beta$ and removes the degeneracy.

## Sources

- S. D. Temple, J. Terhorst, "Pair-based estimators of infection and removal rates for stochastic epidemic models", arXiv:2603.21992 (2026), Section 2 (complete-data MLEs and $\tau_{kj}$-imputation estimator), Proposition 1, and the Appendix lemmas giving $\mathbb E[\tau_{kj}]$ for each partial-observation pattern. <https://doi.org/10.48550/arXiv.2603.21992>
