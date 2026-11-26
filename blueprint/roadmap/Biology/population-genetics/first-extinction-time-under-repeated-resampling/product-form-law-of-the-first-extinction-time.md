# Product-form law of the first-extinction time

**Process.** A distribution $p(t)=(p_1(t),\dots,p_M(t))$ is updated by drawing $N$ samples and setting $p_i(t+1)=n_i(t)/N$. Given $p(t)$, the increment $\Delta p_i$ has mean $0$ and variance $p_i(1-p_i)/N$. Let $\tau_i$ be the time state $i$ is lost and $\tau_{\min}=\min_i\tau_i$.

**Single-state law.** Treating $p_i$ as the zero-drift square-root (Feller) diffusion $dp_i=\sqrt{p_i/N}\,dW_i$, the probability that state $i$ is extinct by time $\tau$ is

$$F_i(\tau)=\exp\Big(-\frac{2Np_i(0)}{\tau}\Big).$$

**First-extinction law.** Treating the states as independent,

$$\mathbb P(\tau_{\min}>\tau)=\prod_{i=1}^M\Big(1-e^{-2Np_i(0)/\tau}\Big),\qquad \langle\tau_{\min}\rangle=\int_0^\infty\prod_{i=1}^M\Big(1-e^{-2Np_i(0)/\tau}\Big)d\tau=2N\int_0^\infty\prod_{i=1}^M\big(1-e^{-xp_i(0)}\big)\frac{dx}{x^2}.$$

So $\langle\tau_{\min}\rangle$ is proportional to $N$ for fixed initial frequencies, and the paper proves that this mean coincides exactly with the Wright–Fisher mean time to the first loss of an allele obtained by Baxter et al. through inclusion–exclusion over subsets of states, while costing $O(M)$ to evaluate.

## Depends on

- [Fixation and absorption in the Wright–Fisher diffusion](../diffusion-theory/fixation-and-absorption-in-the-wright-fisher-dif/README.md)

## Expansion

For the square-root diffusion $dX=\sqrt{X/N}\,dW$, Feller's fundamental solution of the forward equation has an atom at $0$ of mass $\exp(-2NX_0/t)$, the probability of absorption by time $t$. Dropping the factor $1-p_i$ is accurate for the rare states that go extinct first, and the dependence between frequencies imposed by $\sum_ip_i=1$ is weak for the minimum. Expanding the product reproduces the alternating sums over subsets of states of the exact formula, which is why the means agree; the integral form avoids the cancellations.

## Sources

- M. Benati, A. Londei, D. Lanzieri, V. Loreto, "First-Extinction Law for Resampling Processes", arXiv:2509.20101 (2025), main text (square-root diffusion approximation, Eqs. (CDF), (P\_tau\_min>tau), scaling in $N$), Section 2 (Theorems 2.2 and 2.3, Feller's calculation), <https://doi.org/10.48550/arXiv.2509.20101>.
