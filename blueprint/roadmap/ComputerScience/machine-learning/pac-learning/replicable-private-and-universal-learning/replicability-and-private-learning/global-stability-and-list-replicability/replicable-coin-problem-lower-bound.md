# Replicability costs a quadratic factor in the replicability parameter

A randomized algorithm $A(S; r)$ taking an i.i.d. sample $S$ from a distribution $D$ and internal randomness $r$ is **$\rho$-replicable** if $\Pr_{S, S' \sim D^n,\, r}[A(S; r) = A(S'; r)] \ge 1 - \rho$ for every $D$, where $S, S', r$ are independent and the same $r$ is used in both runs. In the **$\tau$-coin problem** one observes i.i.d. bits of bias $p \in [0,1]$ and must output $1$ if $p \ge \tfrac12 + \tau$ and $0$ if $p \le \tfrac12 - \tau$ (either output allowed otherwise). For $0 < \tau < 1/4$, $\rho < 1/16$ and $\delta \le 1/16$, every $\rho$-replicable algorithm solving the $\tau$-coin problem with success probability at least $1 - \delta$ at both biases $\tfrac12 \pm \tau$, the probability being over the samples and the internal randomness together (accuracy averaged over seeds, not required for every seed), needs $\Omega(\tau^{-2} \rho^{-2})$ samples. Some restriction on $\tau$ is needed: for $\tau > 1/2$ neither forced output can ever occur, since no bias lies in $[\tfrac12 + \tau, 1]$ or $[0, \tfrac12 - \tau]$, and the proof uses $\tau < 1/4$ to keep all biases considered in $(1/4, 3/4)$. Without replicability $O(\tau^{-2}\log(1/\delta))$ samples suffice. Hence replicable mean estimation by random grid rounding, which answers a $[0,1]$-valued statistical query to tolerance $\tau$ $\rho$-replicably from $\tilde O(\tau^{-2}\rho^{-2})$ samples (grid width $\tau$, deviation $\Theta(\tau\rho)$), is optimal in its dependence on $\rho$.

## Proof sketch

The accuracy and replicability guarantees hold only on average over the shared randomness $r$, so first pass to a single good seed: by Markov's inequality each of the following holds for at least $3/4$ of the seeds, so some seed $r^*$ satisfies all three: $f_{r^*}(\tfrac12 - \tau) \le 4\delta \le 1/4$, $f_{r^*}(\tfrac12 + \tau) \ge 1 - 4\delta \ge 3/4$, where $f_r(p) = \Pr_S[A(S; r) = 1]$ for bias $p$, and two runs with seed $r^*$ on a bias $p$ drawn uniformly from $[\tfrac12 - \tau, \tfrac12 + \tau]$ disagree with probability at most $4\rho$. Now $f_{r^*}$ is a polynomial of degree $n$ whose derivative is $O(\sqrt{n})$ on $(1/4, 3/4)$, so it lies in $(1/3, 2/3)$ on an interval of length $\Omega(1/\sqrt{n})$ inside $(\tfrac12 - \tau, \tfrac12 + \tau)$. A uniform bias falls there with probability $\Omega(1/(\tau\sqrt{n}))$, and then two independent runs disagree with probability more than $4/9$; hence $4\rho = \Omega(1/(\tau\sqrt{n}))$ and $n = \Omega(1/(\tau^2\rho^2))$.

## Depends on

- [Replicable algorithms with shared randomness](../../../replicable-learning/replicable-algorithms-with-shared-seed.md)

## Proof depends on

- [Replicable bounded-mean and coin-bias estimation](../../../replicable-learning/replicable-mean-estimation.md)

## Sources

- R. Impagliazzo, R. Lei, T. Pitassi, J. Sorrell, "Reproducibility in Learning", STOC (2022), arXiv:2201.08430, Theorems 1.6 and 7.1 and Lemma 7.2.
