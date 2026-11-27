# Posterior-based proof of the transfer theorem for adaptive data analysis

Let $P$ be a distribution on $\mathcal{X}$, $S \sim P^n$, and let a mechanism $M$ interact with an analyst $A$ on $S$: in round $j = 1, \dots, k$ the analyst chooses a linear (statistical) query $q_j : \mathcal{X} \to [0,1]$ depending on the previous answers, and $M$ returns an answer $a_j$; write $q_j(S) = \frac1n \sum_{x \in S} q_j(x)$ and $q_j(P) = \mathbb{E}_{x \sim P}[q_j(x)]$. The mechanism is $(\alpha, \beta)$-sample accurate if for every analyst and every $P$, $\Pr[\max_j \lvert q_j(S) - a_j \rvert \ge \alpha] \le \beta$, and $(\varepsilon, \delta)$-differentially private if for every analyst the transcript $\Pi = ((q_1, a_1), \dots, (q_k, a_k))$ is $(\varepsilon, \delta)$-differentially private as a function of $S$, for datasets differing in one coordinate. If $M$ is $(\varepsilon, \delta)$-differentially private and $(\alpha, \beta)$-sample accurate for linear queries, then for every analyst and all $c, d > 0$,

$$
\Pr\Bigl[\max_j \lvert a_j - q_j(P) \rvert > \alpha + (e^{\varepsilon} - 1) + c + 2d\Bigr] \le \frac{\beta}{c} + \frac{\delta}{d}.
$$

The posterior $Q_\pi$ of $S$ given the transcript $\pi$ need not be a product of independent observations; the proof needs no concentration for it.

## Proof sketch

Bayesian resampling: replacing $S$, after the interaction, by a fresh draw $S'$ from its posterior $Q_\Pi$ does not change the joint law of dataset and transcript. Hence sample accuracy also holds for $S'$, and since each answer is fixed before $S'$ is drawn while $q_j(S') \in [0,1]$, Markov's inequality gives $\max_j \lvert a_j - q_j(Q_\Pi) \rvert \le \alpha + c$ except with probability $\beta/c$, where $q_j(Q_\Pi)$ is the posterior mean of $q_j(S')$. Differential privacy bounds how far the posterior can move any query's mean from its prior value, with boundedness of the queries: $\max_j \lvert q_j(Q_\Pi) - q_j(P) \rvert \le e^{\varepsilon} - 1 + 2d$ except with probability $\delta/d$. A union bound over the two events gives the theorem.

## Depends on

- [Differential privacy](../../differential-privacy/differentially-private.md)

## Sources

- C. Jung, K. Ligett, S. Neel, A. Roth, S. Sharifi-Malvajerdi, M. Shenfeld, "A New Analysis of Differential Privacy's Generalization Guarantees", ITCS (2020), arXiv:1909.03577, Definitions 2.1 and 2.2, Lemmas 3.2–3.4 and Theorem 3.5.
