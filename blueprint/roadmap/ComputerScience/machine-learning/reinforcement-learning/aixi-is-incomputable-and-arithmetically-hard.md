# AIXI is incomputable, and its optimal policies are arithmetically hard

AIXI, Hutter's Bayesian reinforcement learning agent over all lower semicomputable environments, is not computable for any choice of universal machine once there are two actions and rewards $0$ and $1$. Optimal policies for some environments are $\Pi^0_2$-hard, and for some universal machines even $\varepsilon$-optimal AIXI policies solve $\Sigma^0_1$-hard problems.

**Setting (Leike and Hutter).** An agent and an environment interact in cycles: at time $t$ the agent chooses an action $a_t$ from a finite set $\mathcal{A}$ and receives a percept $e_t = (o_t, r_t)$ from a finite set $\mathcal{E}$, with reward $r_t \in [0, 1]$; a *policy* $\pi$ maps histories in $(\mathcal{A} \times \mathcal{E})^*$ to actions. Environments are *lower semicomputable chronological conditional semimeasures* $\nu(e_{1:t} \parallel a_{1:t})$, whose percepts do not depend on future actions; $\mathcal{M}$ is the class of all of them. Fix a lower semicomputable discount function $\gamma$ with $\gamma(t) \ge 0$ and $\sum_t \gamma(t) < \infty$, and write $\Gamma_t = \sum_{i \ge t} \gamma(i)$. The value of $\pi$ in $\nu$ after a history $æ_{<t}$ is

$$
V^\pi_\nu(æ_{<t}) = \frac{1}{\Gamma_t} \sum_{k \ge t} \sum_{e_{t:k}} \gamma(k)\, r_k\, \nu(e_{1:k} \mid e_{<t} \parallel a_{1:k})
$$

when $\Gamma_t > 0$, where the actions $a_i$ for $i \ge t$ are chosen by $\pi$; $\Gamma_t$ is the normalizing denominator and the value is $0$ when $\Gamma_t = 0$. $V^*_\nu = \sup_\pi V^\pi_\nu$, a policy is *$\nu$-optimal* if it attains $V^*_\nu$ after every history, and *$\varepsilon$-optimal* if $V^*_\nu(h) - V^\pi_\nu(h) < \varepsilon$ for every history $h$. *AINU* is a $\nu$-optimal policy. For a universal Turing machine $U$, the *universal mixture* $\xi = \sum_{\nu \in \mathcal{M}} w(\nu)\, \nu$ uses weights $w(\nu) \propto 2^{-K_U(\nu)}$, and *AIXI* is a $\xi$-optimal policy. How ties between equally valued actions are broken is left arbitrary (Section 2.6 of the source); clause 2 below fixes it. Policies are identified with sets of natural numbers by encoding histories, so they can be placed in the arithmetical hierarchy.

**Theorem (Leike and Hutter).** Assume $\Gamma_t > 0$ for all $t$.

1. If $|\mathcal{A}| \ge 2$ and $\mathcal{E}$ contains percepts with reward $0$ and with reward $1$, then for every universal Turing machine $U$ no $\xi$-optimal policy is computable (Theorem 23).
2. Let $\mathcal{A} = \{\alpha, \beta\}$ with $\alpha$ favored in ties and $\mathcal{E} = \mathcal{O} \times \{0, 1\}$ with $\mathcal{O} = \{0, 1\}$. There is an environment $\nu \in \mathcal{M}$ such that AINU, the $\nu$-optimal policy that breaks ties in favor of $\alpha$, is $\Pi^0_2$-hard (Theorem 24).
3. For suitable finite $\mathcal{A}$ and $\mathcal{E}$ (the source takes $\mathcal{A} = \{\alpha, \beta\}$, and its environment also uses the reward $\tfrac12$), there are a universal Turing machine $U'$ and an $\varepsilon > 0$ such that every $\varepsilon$-optimal policy for AIXI with respect to $U'$ is $\Sigma^0_1$-hard (Theorem 25).

Without these hypotheses clause 1 can fail: with one action the only policy is constant, and if every percept has reward $0$ every policy is optimal, so a constant policy is $\xi$-optimal.

These lower bounds complement the paper's upper bounds: for every $\nu \in \mathcal{M}$, some $\nu$-optimal policy is $\Delta^0_3$ and, for every $\varepsilon > 0$, some $\varepsilon$-optimal policy is $\Delta^0_2$. For the iterative value function of Hutter's book the same paper proves that optimal policies are $\Sigma^0_3$-hard for some environment and that, for some universal mixture, $\varepsilon$-optimal iterative AIXI policies are $\Pi^0_2$-hard.

## Depends on

- [The arithmetical class $\Sigma_n$](../../../TheoryOfComputation/degrees-and-hierarchies/arithmetical-hierarchy/is-sigma.md)
- [The arithmetical class $\Pi_n$](../../../TheoryOfComputation/degrees-and-hierarchies/arithmetical-hierarchy/is-pi.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [The class Δₙ of the arithmetical hierarchy](../../../TheoryOfComputation/degrees-and-hierarchies/arithmetical-hierarchy/is-delta.md)

## Proof depends on

None.

## Expansion

For clause 1, if some AIXI policy $\pi^*_\xi$ were computable, the deterministic environment that gives reward $0$ while the agent follows $\pi^*_\xi$ and reward $1$ forever once it deviates would belong to $\mathcal{M}$; since AIXI learns to predict any environment in $\mathcal{M}$ on its own policy, it would eventually deviate, a contradiction. Clause 2 encodes a $\Pi^0_2$ set $A$, with $n \in A$ iff $\forall i\, \exists k\, \eta(n, i, k)$, into a mixture $\nu$ of environments in which, after observing $1^n 0$, the preferred action $\alpha$ ties with the alternative $\beta$ exactly when $n \in A$ and is strictly worse otherwise, so AINU takes $\alpha$ there exactly when $n \in A$. Clause 3 builds a universal machine whose mixture places enough weight on an environment that forces any $\varepsilon$-optimal policy to decide a $\Sigma^0_1$ set. A good expansion links a page for the on-policy value convergence of AIXI in every environment of $\mathcal{M}$, the learning property clause 1 uses.

## Sources

- Jan Leike and Marcus Hutter, *On the computability of Solomonoff induction and AIXI*, Theoretical Computer Science 716 (2018), 28–49, https://doi.org/10.1016/j.tcs.2017.11.020; Section 2.5–2.6 (setting), Corollaries 18 and 21 (upper bounds), Theorems 23, 24 and 25 (lower bounds) and Theorems 30 and 31 (iterative value), read in the accepted manuscript at https://openresearch-repository.anu.edu.au/handle/1885/232674; the conference version, *On the Computability of AIXI* (UAI 2015), was read in arXiv:1510.05572v1.
