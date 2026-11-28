# Exponential separation between model-based and model-free exploration

Some families of at most $2^H$ factored MDPs sharing a reward let a model-based learner given the class find an $\varepsilon$-optimal policy with probability $1-\delta$ from $\mathrm{poly}(H,1/\varepsilon,\log(1/\delta))$ trajectories, while every model-free learner seeing states only via the class's optimal $Q$-functions and policies needs $2^{\Omega(H)}$ trajectories to be $1/2$-optimal with probability over $2/3$.

**Model-free algorithms.** For a finite class $\mathcal{G}$ of functions $\mathcal{X}\times\mathcal{A} \to \mathbb{R}$, the $\mathcal{G}$-profile of a context is $\Phi_{\mathcal{G}}(x) = [g(x,a)]_{g\in\mathcal{G}, a\in\mathcal{A}} \in \mathbb{R}^{|\mathcal{G}|\times|\mathcal{A}|}$. An algorithm is *model-free using $\mathcal{G}$* if, during its whole execution, it accesses every context $x$ only through $\Phi_{\mathcal{G}}(x)$. For a model class $\mathcal{M}$, $\mathrm{OP}(\mathcal{M})$ is the set of optimal $Q$-functions and optimal policies of its models; a model-based algorithm receives $\mathcal{M}$, a model-free one $\mathcal{G} = \mathrm{OP}(\mathcal{M})$.

**Theorem.** Fix $\delta, \varepsilon \in (0,1]$. There is a family $\mathcal{M}$ of contextual decision processes with horizon $H$, all with the same reward function and $|\mathcal{M}| \le 2^H$, such that:

1. for every process in the family, a model-based algorithm using $\mathcal{M}$ as its model class outputs, with probability at least $1-\delta$, a policy $\hat\pi$ with $v^{\hat\pi} \ge v^\star - \varepsilon$ using at most $\mathrm{poly}(H, 1/\varepsilon, \log(1/\delta))$ trajectories;
2. with $\mathcal{G} = \mathrm{OP}(\mathcal{M})$, every model-free algorithm using $o(2^H)$ trajectories outputs, on some process in the family, a policy with $v^{\hat\pi} < v^\star - 1/2$ with probability at least $1/3$.

Here $v^\pi$ is the expected total reward with $\sum_h r_h \le 1$, and the true process belongs to $\mathcal{M}$, so $Q^\star \in \mathcal{G}$ and $\pi^\star \in \mathcal{G}$.

**Scope.** The hard family consists of deterministic factored MDPs with $2^d$ members, $d = H - 2$ state variables in the appendix construction (the main text summarizes it as $d = H$), $|\mathcal{O}| = 4$ values per variable, one parent per variable and two actions. For factored MDPs with known structure and known reward, the source's algorithm needs $\tilde O(d^2L^3HK^2\log(1/\delta)/\varepsilon^2)$ trajectories, where $L$ is the number of transition parameters (Theorem 8). The separation is information-theoretic, about samples, not computation. It concerns model-free methods that see states only through $\mathrm{OP}(\mathcal{M})$; a more expressive $\mathcal{G}$ may reveal the state and avoid the lower bound. Model-based realizability ($M^\star \in \mathcal{M}$) is in general a much stronger assumption than $Q^\star \in \mathcal{G}$.

## Depends on

- [Probability measure](../../../../../Probability/foundations/probability-measures/is-probability-measure.md)

## Proof depends on

- [Witness rank](witness-rank.md)

## Expansion

Each model is indexed by a path $p \in \{-1,1\}^d$. Levels $1$ to $H-1$ form a binary tree whose state variables record the actions taken; the last transition copies the state, except that variable $i$ becomes $2$ if it disagrees with $p_i$. The reward $1$ is paid at level $H$ only in states without the symbol $2$. For the model-free claim the source builds a second, non-factored family $\tilde P^p$ whose last transition sends every state off the path $p$ to the all-$2$ state. That family is indistinguishable from the first through $\mathrm{OP}(\mathcal{M})$-profiles, and in it finding $p$ is a search over $2^d$ paths. For the model-based claim, the factored model class has $K = 2$ and $L = O(H^2)$ parameters, so the guarantee of Theorem 8 applies. That theorem uses uniformly random actions and a test class adapted to the factorization; the witnessed misfit is then a sum of per-factor total variation distances, whose matrix has witness rank at most $L_h/|\mathcal{O}|$.

A complete expansion adds pages for the factored-MDP sample-complexity theorem (Theorem 8, formal version Theorem 20) and for the indistinguishability of the factored and non-factored families through $\mathrm{OP}(\mathcal{M})$-profiles (Appendix C.2.2).

## Sources

- W. Sun, N. Jiang, A. Krishnamurthy, A. Agarwal and J. Langford, "Model-based RL in Contextual Decision Processes: PAC bounds and Exponential Improvements over Model-free Approaches", Conference on Learning Theory (COLT 2019), PMLR 99:2898–2933. Numbers from arXiv:1811.08540v3: Section 2.2 (the operator $\mathrm{OP}$), Definition 1, Theorem 2 and the discussion after it, Section 6 (Theorem 8, Eq. (7)), Appendix C.2 (proof of Theorem 2, Figure 1), Theorem 20 (formal version of Theorem 8). <https://arxiv.org/abs/1811.08540v3>
