# Hitting probabilities of finite birth–death chains

Let $N\ge1$ be an integer. On $\{0,\ldots,N\}$ consider a continuous-time
nearest-neighbor chain with positive finite interior birth and death
rates $\lambda_j,\mu_j$, $1\le j<N$. For hitting times use
$\tau_a=\inf\{t\ge0:X_t=a\}$, so starting at a boundary counts as
hitting it immediately. Boundary rates after the first hit are irrelevant.
Set $\rho_0=1$ and
$\rho_k=\prod_{j=1}^k\mu_j/\lambda_j$ for $1\le k<N$. Then

$$\mathbb P_i(\tau_0<\tau_N)
 =\frac{\sum_{k=i}^{N-1}\rho_k}{\sum_{k=0}^{N-1}\rho_k},
 \qquad 0\le i\le N.$$

The empty numerator at $i=N$ is zero. With equal birth and death rates
the answer is $(N-i)/N$. If the ratio $\lambda_j/\mu_j=r>0$ is
constant, the complementary fixation probability at $N$ is
$(1-r^{-i})/(1-r^{-N})$ when $r\ne1$, and $i/N$ when $r=1$.
This is the ratio check for a correspondingly normalized Moran model,
not an assumption about the model's absolute clock.

## Depends on

- [Finite continuous-time path](../finite-continuous-time-markov-chains-as-path-pro/ctmc-path.md)

## Proof depends on

- [Finite-chain absorption equations](../../finite-markov-chains/absorption-probabilities-and-mean-absorption-tim.md)


## Expansion

The stopped jump chain has up/down probabilities
$\lambda_j/(\lambda_j+\mu_j)$ and $\mu_j/(\lambda_j+\mu_j)$.
Positive interior probabilities give a uniform positive probability of
reaching a boundary in at most $N$ jumps, hence almost-sure absorption.
Its harmonic equation is
$\lambda_j(h_{j+1}-h_j)=\mu_j(h_j-h_{j-1})$.
The proposed expression has increments
$h_{j+1}-h_j=-\rho_j/\sum_{k=0}^{N-1}\rho_k$, which satisfy this
identity and $h_0=1,h_N=0$. Uniqueness of the finite absorption equation
proves the formula. Holding times do not change the first boundary hit.
The geometric-sum specialization yields the constant-ratio check.
The stationary law of a finite birth–death chain, including the more
general allowance of zero births, is a separate canonical theorem and is
not restated here.

## Sources

- R. Durrett, *Probability: Theory and Examples*, 5th edition (2019), <https://services.math.duke.edu/~rtd/PTE/PTE5_011119.pdf>, Example 5.3.9 and Theorem 5.3.10, for the discrete exit-probability recursion. The continuous-time jump-chain translation and boundary convention are explicit above.
