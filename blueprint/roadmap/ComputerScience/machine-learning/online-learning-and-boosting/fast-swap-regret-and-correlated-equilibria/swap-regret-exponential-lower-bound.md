# Exponential dependence on the inverse swap regret is necessary

In online learning with $N$ actions (or a hypothesis class $F$), at each round $t = 1, \dots, T$ the learner chooses a distribution $p_t$ over actions and an adversary chooses a loss vector $\ell_t \in [0,1]^N$. The **(normalized, distributional) swap regret** is

$$
\mathrm{SwapReg}_T = \frac{1}{T}\max_{\phi : [N] \to [N]} \sum_{t=1}^T \sum_{a} p_t(a)\big(\ell_t(a) - \ell_t(\phi(a))\big),
$$

and the learner achieves **$\varepsilon$-swap regret** after $T$ rounds if $\mathbb{E}[\mathrm{SwapReg}_T] \le \varepsilon$ against every adaptive adversary. In the non-distributional variant the learner must play a sampled action rather than a distribution. (i) For every $N$ and $\varepsilon \in (0,1)$ and every number of rounds

$$
T \le c\cdot\min\Big\{ \exp\big(c'\varepsilon^{-1/6}\big),\; \frac{N}{\log^{12}(N)\,\varepsilon^2} \Big\},
$$

there is an oblivious adversary with losses in $\{f \in [0,1]^N : \|f\|_1 \le 1\}$ forcing expected distributional swap regret at least $\varepsilon$; equivalently, swap regret $\tilde\Omega\big(\min(1, \sqrt{N/T})\big)$ is unavoidable in that range. (ii) There is an oblivious adversary such that every algorithm has expected (unnormalized) swap regret $\Omega\big(\min\{T/\log T,\; \sqrt{N^{1-o(1)}T}\}\big)$ over $T$ rounds. Hence the number of rounds must be exponential in $1/\varepsilon$ (unless it is nearly linear in $N$), matching the upper bounds.

## Proof sketch

The adversary builds a hierarchical loss sequence: at each scale it hides a good action among blocks of rounds in a way that any distribution with low external regret at that scale must place mass on actions that become bad at the next scale. Swap regret accumulates across scales because a swap function can redirect each scale's mass separately, and a number of scales polynomial in $1/\varepsilon$ fits within $T$ rounds only if $T$ is exponential in a power of $1/\varepsilon$; the $\ell_1$-bounded losses keep the adversary oblivious.

## Depends on

- [Swap regret polylogarithmic in the number of actions](polylog-rounds-swap-regret.md)

## Proof depends on

- [Swap regret polylogarithmic in the number of actions](polylog-rounds-swap-regret.md)

## Sources

- Y. Dagan, C. Daskalakis, M. Fishelson, N. Golowich, "From External to Swap Regret 2.0: An Efficient Reduction for Large Action Spaces", STOC (2024), arXiv:2310.19786.
- B. Peng, A. Rubinstein, "Fast Swap Regret Minimization and Applications to Approximate Correlated Equilibria", STOC (2024), arXiv:2310.19647.
