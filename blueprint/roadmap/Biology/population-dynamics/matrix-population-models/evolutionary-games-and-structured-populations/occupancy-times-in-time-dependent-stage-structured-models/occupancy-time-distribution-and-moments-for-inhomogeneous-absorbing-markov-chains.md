# Occupancy time distribution and moments for inhomogeneous absorbing Markov chains

**Setting.** An individual moves among life-cycle stages $S=\{1,\dots,d\}$ in discrete time. Environmental change makes the transitions time-dependent: $B(n)\in\mathbb R^{d\times d}$ is column sub-stochastic, $B_{ij}(n)$ is the probability of moving from stage $j$ to stage $i$ between times $n$ and $n+1$, and the column deficit is mortality. Put $\Phi(n,m)=B(n-1)\cdots B(m)$ and the death-probability vector $b(n)=(\mathrm{Id}-B(n))^T\mathbf 1_d$. Adding an absorbing death state gives an inhomogeneous Markov chain $(X_n)$ started from the stage distribution $v$, with lifetime $N=\min\{n:X_n=\text{dead}\}$.

For $R\subset S$ (identified with the diagonal $0/1$ matrix projecting onto $R$), the *$R$-occupancy time* up to $n$ is $A_R(n)=\#\{k<n:X_k\in R\}$, and the *lifetime occupancy* is $\tau_R=A_R(N)$, e.g. the number of breeding attempts when $R$ is the set of breeder stages. Let $p^R(a,n)\in\mathbb R^d$ have entries $p^R_j(a,n)=\mathbb P\{X_n=j,\ A_R(n)=a\}$.

**Theorem.**

1. *(Lifetime.)* $\mathbb P\{N=n\}=b(n-1)^T\Phi(n-1,0)v$ for $n\ge1$.
2. *(Occupancy recursion.)* $p^R(a,n)$ solves the discrete McKendrick–von Foerster equation

$$
p^R_j(a,n+1)=\sum_{k\notin R}B_{jk}(n)\,p^R_k(a,n)+\sum_{k\in R}B_{jk}(n)\,p^R_k(a-1,n),
$$

   with $p^R(0,0)=v$, $p^R(a,0)=0$ for $a>0$, and boundary condition $p^R_j(0,n+1)=\sum_{k\notin R}B_{jk}(n)p^R_k(0,n)$.
3. *(Distribution.)* For $a\in\mathbb N_0$,

$$
\mathbb P\{\tau_R=a\}=\sum_{n=0}^\infty b(n)^T\big(R\,p^R(a-1,n)+(\mathrm{Id}-R)\,p^R(a,n)\big).
$$

4. *(Moments.)* With $m^R_k(n)=\sum_{a=1}^n a^k p^R(a,n)$ (and $m_0^R(n)=\sum_{a\ge0}p^R(a,n)$),

$$
\mathbb E(\tau_R^k)=\sum_{n=0}^\infty b(n)^T\Big(m_k^R(n)+R\sum_{j=1}^k\binom kj m^R_{k-j}(n)\Big),\qquad k\ge1,
$$

   where $m^R_0(n+1)=B(n)m_0^R(n)$ and $m_k^R(n+1)=B(n)\big(m_k^R(n)+R\sum_{j=1}^k\binom kj m^R_{k-j}(n)\big)$, with $m_0^R(0)=v$ and $m_k^R(0)=0$.

## Expansion

Occupancy time plays the role of "age" in a structured population: each step spent in $R$ increments it by one, which is exactly the age-shift structure of the McKendrick–von Foerster equation. Death at time $n$ from stage $j$ has probability $b_j(n)$; if $j\in R$ the final step is counted, hence the split between $Rp^R(a-1,n)$ and $(\mathrm{Id}-R)p^R(a,n)$. The moment recursions come from expanding $(a+1)^k$ binomially for transitions out of $R$ and avoid computing the full distribution. In the time-homogeneous case $B(n)\equiv B$ the series collapse to fundamental-matrix expressions, e.g. $\mathbb E\tau_R=\mathbf 1^T R(\mathrm{Id}-B)^{-1}v$ (expected number of visits to $R$ before death); the time-dependent version captures, e.g., how breeding attempts of Southern Fulmars depend on directional or random environmental trends.

## Sources

- George Chappelle, Alan Hastings, Martin Rasmussen, "Occupancy times for time-dependent stage-structured models", arXiv:2012.00196 (2020), Section 2: Propositions 1–3, Definition 1, Theorem 1; Section 3 (Southern Fulmar application), <https://doi.org/10.48550/arXiv.2012.00196>.
