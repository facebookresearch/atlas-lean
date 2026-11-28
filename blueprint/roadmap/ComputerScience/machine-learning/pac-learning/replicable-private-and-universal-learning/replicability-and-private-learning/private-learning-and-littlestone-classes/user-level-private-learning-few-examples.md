# User-level private learning from item-level private learning with few examples per user

In **user-level** differential privacy the dataset consists of $n$ users each contributing $m$ examples, and neighbouring datasets may differ in all examples of one user. Algorithms have a finite output space (Ghazi et al. make this assumption throughout, footnote 1). The input consists of $nm$ i.i.d. samples from an unknown distribution $\mathcal{D}$, split among the users; a task $T$ specifies, for each valid $\mathcal{D}$, a set of correct answers, and an algorithm is $\gamma$-useful for $T$ if its output is correct with probability at least $\gamma$ for every valid $\mathcal{D}$. Let $n_m(\varepsilon,\delta;\gamma)$ be the least number of users for which some $(\varepsilon,\delta)$-user-level private algorithm is $\gamma$-useful with $m$ examples per user ($n_1$ is the item-level sample complexity). For approximate differential privacy, for every task, every $\gamma > 0$, all sufficiently small $\varepsilon, \delta > 0$ (at most an absolute constant) and every $m \in \mathbb{N}$, with item-level parameters

$$
\varepsilon' = \frac{\varepsilon^2}{\log(1/\delta)\sqrt{m \log(m/\delta)}}, \qquad \delta' = \Theta\Big(\frac{\delta\,\varepsilon}{m \log(1/\delta)}\Big),
$$

one has (Theorem 10)

$$
n_m(\varepsilon, \delta; \gamma - o(1)) \le \tilde O\Big(\frac{\log(1/\delta)}{\varepsilon} + \frac{1}{m}\, n_1(\varepsilon', \delta'; \gamma)\Big).
$$

A subsampling step makes the two privacy parameters $\varepsilon$ equal, but not the two $\delta$s: with the same $\delta' = \Theta\big(\delta\varepsilon/(m\log(1/\delta))\big)$ (Theorem 11),

$$
n_m(\varepsilon, \delta; \gamma - o(1)) \le \tilde O\Big(\frac{\log(1/\delta)}{\varepsilon} + \frac{1}{\sqrt{m}} \cdot \frac{\log(1/\delta)^{1.5}}{\varepsilon} \cdot n_1(\varepsilon, \delta'; \gamma)\Big),
$$

so for item-level complexities depending only polylogarithmically on $1/\delta$ the number of users drops by a factor of roughly $\sqrt{m}$, up to factors polylogarithmic in $1/\delta$ and $m$. These are upper bounds achieved by one construction: its additive $\log(1/\delta)/\varepsilon$ users are the users it deletes, an overhead of this construction rather than a lower bound for every task (a task in which one fixed output is correct for every valid $\mathcal{D}$ needs no users at all). For pure differential privacy, an adaptation of the exponential mechanism to the user level gives new bounds for private PAC learning, hypothesis selection and distribution learning, which are near-optimal for some of these tasks.

## Proof sketch

The approximate-privacy transformation is a propose-test-release construction around the item-level algorithm $A$. An item-level private algorithm is, with high probability over i.i.d. data, perfectly generalizing, so deleting any $r$ users changes its output distribution only by privacy loss about $\varepsilon' r\sqrt{m}$ rather than $\varepsilon' r m$ (local-deletion privacy at the input). The algorithm draws a noisy target size $R_1$ from a truncated discrete Laplace distribution on $\{0, \dots, 2\kappa\}$ with $\kappa = O(\log(1/\delta)/\varepsilon)$, tests whether some set $S$ of $R_1$ users has the property that $A$ is local-deletion private at the input with $S$ removed (a test of the input's distance to unstable inputs), returns the abort symbol $\bot$ if no such set exists, and otherwise removes a random superset $T \supseteq S$ of $4\kappa$ users and returns $A$ run on the remaining data. The $4\kappa$ deleted users give the additive $\log(1/\delta)/\varepsilon$ term. The pure-privacy result scores candidate outputs by the number of users whose data is well explained and applies the exponential mechanism with user-level sensitivity one.

## Depends on

- [Private PAC learners and their sample complexity](private-pac-learner.md)
- [Differential privacy](../../../../../cryptography/differential-privacy/differentially-private.md)

## Proof depends on

- [The exponential mechanism is differentially private](../../../../../cryptography/laplace-and-exponential-mechanisms/exp-mechanism-differentially-private.md)

## Sources

- B. Ghazi, P. Kamath, R. Kumar, P. Manurangsi, R. Meka, C. Zhang, "User-Level Differential Privacy With Few Examples Per User", NeurIPS (2023), arXiv:2309.12500, footnote 1, Definitions 1 and 2 and the task model after them, Theorems 10, 11 and 17, Algorithm 1 and Lemmas 18 and 19.
- M. Bun, M. Gaboardi, M. Hopkins, R. Impagliazzo, R. Lei, T. Pitassi, S. Sivakumar, J. Sorrell, "Stability is Stable: Connections between Replicability, Privacy, and Adaptive Generalization", STOC (2023), arXiv:2303.12921.
