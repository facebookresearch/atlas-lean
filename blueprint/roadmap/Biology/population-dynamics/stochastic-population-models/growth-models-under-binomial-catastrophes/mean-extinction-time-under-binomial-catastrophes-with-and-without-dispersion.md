# Mean extinction time under binomial catastrophes with and without dispersion

**Binomial catastrophe.** At a catastrophe, a colony of size $i$ drops to $j$ with probability $\binom{i}{j}p^j(1-p)^{i-j}$, $0 \le j \le i$, where $p \in (0,1)$ is the individual survival probability.

**Models.** In each model a colony starts with one individual, gains individuals as a Poisson process of rate $\lambda > 0$, and is struck by catastrophes at rate $1$.
- $C(\lambda, p)$, *no dispersion*: survivors stay in the colony. Extinction time $\tau_A$.
- $C_d(\lambda, p)$, *dispersion on a tree*: on the rooted tree with $d$ children per vertex, after a catastrophe each survivor moves to a uniformly chosen child vertex; at each child that receives survivors exactly one founds a new colony and the rest die. Extinction time $\tau_d$.
- $C_*(\lambda, p)$, *dispersion without spatial restriction*: every survivor founds its own new colony. Extinction time $\tau_*$.

**Theorem.**
1. For $C(\lambda, p)$, extinction is certain and

$$
\mathbb{E}[\tau_A] = \frac{1}{\lambda}\left(\prod_{k=0}^{\infty} (1 + \lambda p^k) - 1\right).
$$

2. For $d = 2$: if $p < 2/(\lambda + 2)$,

$$
\mathbb{E}[\tau_2] = \frac{(\lambda p + 1)(\lambda p + 2)}{\lambda p^2 (\lambda + 1)} \ln\left[\frac{(1-p)(\lambda p + 2)}{(1-p)(\lambda p + 2) - \lambda p^2 (\lambda + 1)}\right],
$$

and $\mathbb{E}[\tau_2] = \infty$ at $p = 2/(\lambda + 2)$. An analogous closed form holds for $d = 3$ when $p < 3/(2\lambda + 3)$.
3. For $C_*(\lambda, p)$: if $p < 1/(\lambda + 1)$,

$$
\mathbb{E}[\tau_*] = 1 - \frac{\lambda + 1}{\lambda} \ln\left[1 - \frac{\lambda p}{1 - p}\right],
$$

and $\mathbb{E}[\tau_*] = \infty$ at $p = 1/(\lambda + 1)$.
4. *(Comparison.)* If $p < 1/(\lambda + 1)$, then $\mathbb{E}[\tau_A] < \mathbb{E}[\tau_*]$: unrestricted dispersion always prolongs the mean time to extinction. Whether $\mathbb{E}[\tau_A] < \mathbb{E}[\tau_2]$ (resp. $\mathbb{E}[\tau_3]$) holds is decided by comparing the $q$-product $\prod_k (1 + \lambda p^k)$ with the explicit logarithmic expressions, and either strategy can win depending on $(\lambda, p)$.

## Proof sketch

Without dispersion the colony size is a Markov chain on $\{0, 1, \dots\}$ whose return-to-zero time has a $q$-product mean, because surviving $k$ successive catastrophes thins each individual by $p^k$. With dispersion, colonies evolve independently, so the number of colonies is a continuous-time Galton–Watson process: each colony lives an exponential time, during which its size grows as a Poisson process, and is then replaced by the number of target sites that receive survivors. The extinction time of a (sub)critical branching process with quadratic or cubic offspring generating function has an explicit mean by integrating $\int_0^1 ds/(f(s) - s)$, which produces the logarithms; criticality ($f'(1) = 1$) gives the thresholds $p = 2/(\lambda+2)$, $3/(2\lambda+3)$ and $1/(\lambda+1)$.

## Sources

- F. Duque, V. V. Junior, F. P. Machado and A. Roldán-Correa, "Extinction time in growth models subject to binomial catastrophes *", *Journal of Statistical Mechanics: Theory and Experiment* 2023 (2023), 103501, <https://doi.org/10.1088/1742-5468/acf8bc>. Preprint version: arXiv:2302.02826 (2023), Section 2, Theorems 2.1–2.3, Propositions 3.1–3.3, Lemma 4.1, <https://doi.org/10.48550/arXiv.2302.02826>.
