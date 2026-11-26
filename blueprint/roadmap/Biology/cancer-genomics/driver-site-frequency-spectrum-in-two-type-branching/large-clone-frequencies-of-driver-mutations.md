# Large-clone frequencies of driver mutations

**Setting.** As in the two-type driver model: type-0 cells divide at rate $a$ and die at rate $d$, producing a type-1 mutant offspring with probability $v$ per division and mutating at rate $\mu$; type-1 cells divide at rate $a+b$ and die at rate $d$, with $\lambda_0=a(1-v)-d-\mu>0$ and $\lambda_1=a+b-d>\lambda_0$. Let $T_i$ be the founding time of the $i$-th driver clone, $Z_1^{(i)}(s)$ its size $s$ time units later, $Y_1^{(i)}=\lim_{s\to\infty}e^{-\lambda_1 s}Z_1^{(i)}(s)$ (zero with probability $p_1=d/(a+b)$, otherwise exponential with rate $q_1=1-p_1$), $Y=\lim_t e^{-\lambda_0 t}Z_0(t)$, and $W=\lim_t e^{-\lambda_1 t}Z_1(t)=\sum_i e^{-\lambda_1 T_i}Y_1^{(i)}$. For $0<f<1$ the **relative driver spectrum** $R_f(t)$ is the number of driver clones whose size exceeds $fZ_1(t)$; $\Omega_0^\infty$ is survival of the type-0 population and $\tau_n$ the hitting time of total size $n$.

**Theorem 4 (frequencies of large clones).** Almost surely on $\Omega_0^\infty$,

$$\lim_{n\to\infty}R_f(\tau_n)=\lim_{t\to\infty}R_f(t)=\sum_{i\in\mathbb{N}}\mathbf{1}\{e^{-\lambda_1 T_i}Y_1^{(i)}>Wf\},$$

$$\lim_{f\to0^+}\lim_{t\to\infty}f^{\lambda_0/\lambda_1}R_f(t)=\frac{(av+\mu)\,q_1^{1-\lambda_0/\lambda_1}}{\lambda_1}\,\Gamma\!\left(\frac{\lambda_0}{\lambda_1}\right)Y\,W^{-\lambda_0/\lambda_1},$$

with the same limit along $\tau_n$; and the largest clone frequency $\max_{i:T_i\le t}Z_1^{(i)}(t-T_i)/Z_1(t)$ converges to $\sup_i e^{-\lambda_1 T_i}Y_1^{(i)}/W$.

**Proposition 7 (rare-mutation limit).** If $\mu=0$ and $v\to0^+$, the small-frequency limit $\lim_{f\to0^+}\lim_{t\to\infty}f^{\lambda_0/\lambda_1}R_f(t)$, conditioned on $\Omega_0^\infty$, converges in law to a variable $R^*$ with Laplace transform $E_\alpha(-Cx)$, where $\alpha$ is the limiting ratio $\lambda_0/\lambda_1$, $E_\alpha$ is the Mittag-Leffler function and $C=\Gamma(\alpha)\sin(\pi\alpha)/\pi$.

## Expansion

All type-1 clones grow at the same exponential rate $\lambda_1$, so the frequency of clone $i$ freezes at $e^{-\lambda_1 T_i}Y_1^{(i)}/W$ and the count above frequency $f$ converges to a functional of the point process $\{(T_i,Y_1^{(i)})\}$. As $f\to0$, founding times are asymptotically Poisson with intensity $(av+\mu)Ye^{\lambda_0 s}$; integrating $\mathbb{P}(Y_1>fWe^{\lambda_1 s})=q_1e^{-q_1fWe^{\lambda_1 s}}$ against this intensity produces the $f^{-\lambda_0/\lambda_1}$ law with the Gamma-function constant. In the rare-mutation limit, $(Y,v^{-\lambda_1/\lambda_0}W)$ converge jointly to a law whose Laplace transform makes $YW^{-\alpha}$ Mittag-Leffler distributed.

## Sources

- A. Ahmed, J. Foo, E. Gunnarsson, K. Leder, "The site frequency spectrum in an exponentially growing population with selection", arXiv preprint (2026), Theorem 4 and Proposition 7 (Section 3.3), <https://doi.org/10.48550/arXiv.2607.16479>.
