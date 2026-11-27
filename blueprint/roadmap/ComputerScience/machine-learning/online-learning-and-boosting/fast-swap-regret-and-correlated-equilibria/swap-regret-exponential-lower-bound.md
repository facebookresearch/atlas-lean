# Exponential dependence on the inverse swap regret is necessary

In online learning with $N$ actions (or a hypothesis class $F$), at each round $t = 1, \dots, T$ the learner chooses a distribution $p_t$ over actions and an adversary chooses a loss vector $\ell_t \in [0,1]^N$. The **(normalized, distributional) swap regret** is

$$
\mathrm{SwapReg}_T = \frac{1}{T}\max_{\phi : [N] \to [N]} \sum_{t=1}^T \sum_{a} p_t(a)\big(\ell_t(a) - \ell_t(\phi(a))\big),
$$

and the learner achieves **$\varepsilon$-swap regret** after $T$ rounds if $\mathbb{E}[\mathrm{SwapReg}_T] \le \varepsilon$ against every adaptive adversary. In the non-distributional variant the learner must play a sampled action rather than a distribution. (i) For every $N$ and $\varepsilon \in (0,1)$ and every number of rounds

$$
T \le c\cdot\min\Big\{ \exp\big(c'\varepsilon^{-1/6}\big),\; \frac{N}{\log^{12}(N)\,\varepsilon^2} \Big\},
$$

there is an oblivious adversary, drawing reward vectors $u$ from $\{u \in [0,1]^N : \|u\|_1 \le 1\}$ (equivalently losses $\ell = \mathbf{1} - u$, which have the same swap regret), forcing expected distributional swap regret at least $\varepsilon$; equivalently, swap regret $\tilde\Omega\big(\min(1, \sqrt{N/T})\big)$ is unavoidable in that range. (ii) There is an oblivious adversary such that every algorithm has expected (unnormalized) swap regret $\Omega\big(\min\{T/\log T,\; \sqrt{N^{1-o(1)}T}\}\big)$ over $T$ rounds. Hence the number of rounds must be exponential in a power of $1/\varepsilon$, at least $\exp(\Omega(\varepsilon^{-1/6}))$ (unless it is nearly linear in $N$), qualitatively matching the $(\log(N)/\varepsilon^2)^{O(1/\varepsilon)}$ upper bounds.

## Proof sketch

For (i), the adversary uses a complete binary tree of depth $D$ with two actions $a_v, \dot a_v$ at every node and splits time into $2^D$ batches, one per leaf in depth-first order. During the batch of a leaf, only the actions on its root-to-leaf path are rewarded: an internal node at depth $d$ gives reward $d/(2D)$ to $a_v$ while the leaf lies to its left and, once the leaf lies to its right, to $a_v$ or $\dot a_v$ according to a fair coin drawn in advance, and the leaf rewards one of its two actions by a fresh fair coin each round. All coins are drawn before play, so the adversary is oblivious; every reward vector has the same $\ell_1$ norm, and rescaling makes it at most $1$. With $D = \log_2\min\{T, (N+2)/4\}$ and batches of size $T/2^D$, the analysis shows that every learner incurs expected swap regret $\tilde\Omega(\min\{1, \sqrt{N/T}\})$ on this distribution; the coins hide which action of each node will carry the reward later, and the swap function exploits the resulting misallocation separately at each depth. Part (ii) is a separate construction of Peng and Rubinstein.

## Depends on

- [Swap regret](../../../../GameTheory/not-yet-classified/part-02/regret/swap-regret.md)

## Sources

- Y. Dagan, C. Daskalakis, M. Fishelson, N. Golowich, "From External to Swap Regret 2.0: An Efficient Reduction for Large Action Spaces", STOC (2024), arXiv:2310.19786, Corollary 4.2 and Theorem 1.7.
- B. Peng, A. Rubinstein, "Fast Swap Regret Minimization and Applications to Approximate Correlated Equilibria", STOC (2024), arXiv:2310.19647, Theorem 1.2.
