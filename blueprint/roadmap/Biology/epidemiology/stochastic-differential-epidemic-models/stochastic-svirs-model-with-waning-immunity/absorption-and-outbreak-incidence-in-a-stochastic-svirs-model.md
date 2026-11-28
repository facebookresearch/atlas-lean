# Absorption and outbreak incidence in a stochastic SVIRS model with waning immunity

**Model.** In a closed population of size $N$, the numbers of infectious $I(t)$, unprotected susceptible $S(t)$ and vaccinated $V(t)$ individuals (with $R = N - I - S - V$ temporarily immune) form a continuous-time Markov chain on $\mathcal{S} = \{(i,s,v) : i,s,v \ge 0,\ i + s + v \le N\}$ with transitions

| event | new state | rate |
|---|---|---|
| infection of a susceptible | $(i+1, s-1, v)$ | $\beta i s$ |
| infection of a vaccinated individual (vaccine failure) | $(i+1, s, v-1)$ | $h\beta i v$ |
| recovery | $(i-1, s, v)$ | $\gamma i$ |
| vaccination | $(i, s-1, v+1)$ | $\rho s$ |
| loss of vaccine protection | $(i, s+1, v-1)$ | $\theta v$ |
| loss of temporary immunity | $(i, s+1, v)$ | $\epsilon(N - i - s - v)$ |

with $\beta, \gamma, \epsilon, \rho, \theta > 0$ and vaccine failure factor $h \in [0,1]$.

**Long-term behaviour.** The states with neither infectious nor recovered individuals, $\mathcal{S}_A = \{(0, s, N-s) : 0 \le s \le N\}$, form a single closed communicating class; all other states are transient, so the epidemic dies out with probability one, in finite expected time. On $\mathcal{S}_A$ the chain is a finite birth–death process of the susceptible count driven by vaccination and waning protection, and its stationary law is binomial:

$$p_s = \binom{N}{s}\Big(\frac{1}{1 + \rho/\theta}\Big)^{s}\Big(\frac{\rho/\theta}{1 + \rho/\theta}\Big)^{N-s}, \qquad 0 \le s \le N,$$

so each individual is independently susceptible with probability $\theta/(\theta + \rho)$ in the long run.

**Theorem (incidence of an outbreak).** Partition $\mathcal{S}$ into levels $\mathcal{S}(i)$ of states with $i$ infectious individuals ($c_i = \binom{N-i+2}{2}$ states each); the generator is block tridiagonal with blocks $\mathbf A_{i,i'}$. Let $Z$ be the number of new infections occurring before the outbreak, started from one infectious individual, ends. Then:
1. the tail probability vectors $\mathbf x_i^k = \big(\mathbb{P}(Z \ge k \mid \text{start in } (i,s,v))\big)_{(i,s,v) \in \mathcal{S}(i)}$ satisfy $\mathbf x_i^0 = \mathbf 1$, $\mathbf x_0^k = \mathbf 0$ for $k \ge 1$, and for $k \ge 1$ and $1 \le i \le N$

$$\mathbf x_i^k = -\mathbf A_{i,i}^{-1}\sum_{m=1}^{i}\Big[\prod_{j=i-1}^{m}\mathbf A_{j+1,j}\big(-\mathbf A_{j,j}^{-1}\big)\Big]\mathbf d_m^k, \qquad \mathbf d_m^k = (1 - \delta_{m,N})\,\mathbf A_{m,m+1}\mathbf x_{m+1}^{k-1},$$

where the product is taken with $j$ decreasing from $i-1$ on the left to $m$ on the right, and the empty product ($m = i$) is the identity;
2. the factorial moments $\mathbf m_i^k$ of $Z$ satisfy $\mathbf m_i^0 = \mathbf 1$, $\mathbf m_0^k = \mathbf 0$ for $k \ge 1$, and, for $k \ge 1$, $\mathbf m_N^k = -\mathbf B_{N,N}^{-1}\mathbf C_N^k$ and $\mathbf m_i^k = -\mathbf B_{i,i}^{-1}(\mathbf A_{i,i+1}\mathbf m_{i+1}^k + \mathbf C_i^k)$ for $1 \le i \le N-1$, where

$$\mathbf B_{1,1} = \mathbf A_{1,1},\quad \mathbf B_{i,i} = \mathbf A_{i,i} - \mathbf A_{i,i-1}\mathbf B_{i-1,i-1}^{-1}\mathbf A_{i-1,i},\qquad \mathbf C_1^k = \mathbf D_1^k,\quad \mathbf C_i^k = \mathbf D_i^k - \mathbf A_{i,i-1}\mathbf B_{i-1,i-1}^{-1}\mathbf C_{i-1}^k \quad (2 \le i \le N),$$

with $\mathbf D_i^k = (1 - \delta_{i,N})\,k\,\mathbf A_{i,i+1}\mathbf m_{i+1}^{k-1}$.

These give the exact distribution, mean and variance of outbreak incidence, and quantify how vaccination before or during an outbreak lowers it.

## Proof sketch

The absorbing class consists of the states with $i = 0$ and $R = 0$, where only vaccination and waning of vaccine protection act, each person switching independently between susceptible (rate $\rho$ to vaccinated) and vaccinated (rate $\theta$ back), which explains the binomial law. Incidence counts infection transitions, which move the chain up one level; conditioning on the first jump gives a linear system for $\mathbf x^k$ in terms of $\mathbf x^{k-1}$ (an upward jump uses up one infection), level by level this reads $-\mathbf A_{i,i-1}\mathbf x_{i-1}^k - \mathbf A_{i,i}\mathbf x_i^k = \mathbf d_i^k$, and for the moments (differentiating the generating functions $k$ times at $z = 1$) $-\mathbf A_{i,i-1}\mathbf m_{i-1}^k - \mathbf A_{i,i}\mathbf m_i^k - (1-\delta_{i,N})\mathbf A_{i,i+1}\mathbf m_{i+1}^k = \mathbf D_i^k$. The block-tridiagonal structure lets these be solved by forward elimination and back substitution, avoiding the inversion of the full generator of size $\binom{N+3}{3}$.

## Sources

- M. J. Lopez-Herrero and D. Taipe, "Disease Incidence in a Stochastic SVIRS Model with Waning Immunity", in *Lecture Notes in Computer Science*, Springer Nature Switzerland, 2025, 199–212, <https://doi.org/10.1007/978-3-031-83885-9_19>. Preprint version: arXiv:2410.14883 (2024), model description and subsection on long-term behaviour (Section 2), and the two theorems of the section on incidence during an outbreak, <https://doi.org/10.48550/arXiv.2410.14883>.
