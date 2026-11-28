# Exact expected tumor site frequency spectrum and the transition from 1/j² to 1/j

**Model.** A tumor starts from one cell; each cell divides at rate $r_0$ and dies at rate $d_0<r_0$, so $Z_0(t)$ is a supercritical binary birth–death process with net growth rate $\lambda_0=r_0-d_0$, extinction probability $p_0=d_0/r_0$ and survival probability $q_0=\lambda_0/r_0$. At each division the daughter cells acquire new neutral mutations, $w$ on average per division, under the infinite-sites assumption. $S_j(t)$ is the number of mutations carried by exactly $j$ cells at time $t$; $\tilde S_j(t)$ is the same count among **skeleton** cells (cells with an infinite line of descent). Let $t_N=\log(q_0N+p_0)/\lambda_0$ (the time at which a surviving tumor has expected size $N$) and $\tau_N=\inf\{t:Z_0(t)=N\}$.

**Proposition (skeleton spectrum, Proposition 1).** For the skeleton at the corresponding fixed time $\tilde t_N$, for all $N,j\ge1$,

$$
\mathbb E[\tilde S_j(\tilde t_N)]=\frac{w}{q_0}N\int_0^{1-1/N}(1-y)y^{j-1}\,dy=\frac{w}{q_0}N\Bigl(1-\frac1N\Bigr)^j\Bigl(\frac{1}{j(j+1)}+\frac1N\frac{1}{j+1}\Bigr),
$$

a $1/j^2$ law depending on $w$ and $p_0$ only through the effective rate $w/q_0$.

**Proposition (total population, Proposition 2).** For all $N,j\ge1$,

$$
\mathbb E\bigl[S_j(t_N)\bigm|Z_0(t_N)>0\bigr]=wN\int_0^{1-1/N}\frac{(1-y)\,y^{j-1}}{1-p_0y}\,dy\ \sim\ wN\sum_{k=0}^\infty\frac{p_0^k}{(j+k)(j+k+1)}\qquad(N\to\infty).
$$

The fixed-size spectrum $\mathbb E[S_j(\tau_N)\mid\tau_N<\infty]=(w/q_0)\sum_{k=1}^{N-1}(1-p_0^{N-k})\,h^{(j,N-j)}_{(1,k)}$ is given through the solution $h$ of an explicit sparse linear system (hitting probabilities of a two-type embedded chain); for $p_0=0$ it equals $wN/(j(j+1))$ exactly for $2\le j\le N-1$.

**Transition between power laws.** For fixed $0<p_0<1$, the large-$N$ fixed-time spectrum satisfies

$$
wN\sum_{k\ge0}\frac{p_0^k}{(j+k)(j+k+1)}\sim\frac{w}{q_0}N\,\frac{1}{j(j+1)}\quad(j\to\infty),\qquad wN\sum_{k\ge0}\frac{p_0^k}{(j+k)(j+k+1)}\sim\frac{wN}{j}\quad(p_0\to1),
$$

so high-frequency mutations follow the skeleton's $1/j^2$ law while, as death approaches birth, the low-frequency end approaches the $1/j$ spectrum of a constant-size Moran population. Mutation rate scales the spectrum linearly; only the death-to-birth ratio changes its shape.

## Expansion

A mutation arising in a division at time $s$ is carried at time $t$ by the descendants of one daughter, whose number is distributed as $Z_0(t-s)$ started from one cell; integrating the expected division rate $r_0\,\mathbb E[Z_0(s)]$ against $\mathbb P(Z_0(t-s)=j)$, which is geometric-type for the birth–death process, and changing variables to $y=1-e^{-\lambda_0(t-s)}$-type coordinates gives the integral with kernel $(1-y)y^{j-1}/(1-p_0y)$. The skeleton is itself a Yule process with rate $\lambda_0$ in which mutations accrue at effective rate $w/q_0$, giving the pure $(1-y)y^{j-1}$ kernel. Expanding $(1-p_0y)^{-1}=\sum_kp_0^ky^k$ and integrating termwise gives the series; its $j\to\infty$ and $p_0\to1$ asymptotics follow from comparing the series with integrals.

## Proof depends on

- [Kendall's law of the linear birth–death process](../../../../../Probability/branching-processes/linear-birth-death-process/prob.md)

## Sources

- E. B. Gunnarsson, K. Leder and J. Foo, "Exact site frequency spectra of neutrally evolving tumors: a transition between power laws reveals a signature of cell viability", arXiv:2102.11959 (2021), Section 2 (model, Eqs. for $t_N$ and $\tau_N$), Section 3 (Proposition 1), Section 4 (Proposition 2 and Eqs. for the power-law transition) and the appendices with proofs and asymptotics, <https://doi.org/10.48550/arXiv.2102.11959>.
