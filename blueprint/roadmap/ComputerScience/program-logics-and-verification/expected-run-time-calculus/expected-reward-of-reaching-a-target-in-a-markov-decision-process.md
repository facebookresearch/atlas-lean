# Expected reward of reaching a target in a Markov decision process

A *Markov decision process with state rewards* is a tuple $M = (S, \mathit{Act}, P, s_0, \mathit{rew})$ of a countable set $S$ of states, a finite set $\mathit{Act}$ of actions, a transition probability function $P : S \times \mathit{Act} \times S \to [0, 1]$ with $\sum_{s'} P(s, \alpha, s') \in \{0, 1\}$ for all $s$ and $\alpha$, an initial state $s_0$ and a reward function $\mathit{rew} : S \to \mathbb{R}_{\ge 0}$. A *scheduler* $\mathfrak{S} : S^+ \to \mathit{Act}$ selects an action for each nonempty finite sequence of visited states and induces a Markov chain $M_{\mathfrak{S}}$. The cumulative reward of a finite path $\hat\pi = s_0 \dots s_n$ is $\mathit{rew}(\hat\pi) = \sum_{k=0}^{n-1} \mathit{rew}(s_k)$, and its probability under $\mathfrak{S}$ is $\Pr^{M_{\mathfrak{S}}}\{\hat\pi\} = \prod_{k=0}^{|\hat\pi|-1} P(s_k, \mathfrak{S}(s_0 \dots s_k), s_{k+1})$. For a nonempty target set $T \subseteq S$ and a state $s$, let $\Pi(s, T)$ be the set of finite paths from $s$ that end in their first visit to $T$. The *expected reward of eventually reaching $T$ from $s$* is

$$\mathrm{ExpRew}^M(s \models \Diamond T) = \sup_{\mathfrak{S}} \sum_{\hat\pi \in \Pi(s, T)} \Pr^{M_{\mathfrak{S}}}\{\hat\pi\} \cdot \mathit{rew}(\hat\pi)$$

if $\inf_{\mathfrak{S}} \sum_{\hat\pi \in \Pi(s, T)} \Pr^{M_{\mathfrak{S}}}\{\hat\pi\} = 1$, and $\infty$ otherwise.

## Sources

- B. L. Kaminski, J.-P. Katoen, C. Matheja and F. Olmedo, "Weakest precondition reasoning for expected run-times of probabilistic programs", *ESOP 2016*, LNCS 9632, Springer, 2016; extended version arXiv:1601.01001v2, <https://arxiv.org/abs/1601.01001v2>, Section 4 (Markov decision processes, schedulers, cumulative reward and expected reward).
