# Posterior-based proof of the transfer theorem for adaptive data analysis

Let $M$ interact with an analyst on a dataset $S \sim D^n$, answering adaptively chosen statistical queries, and let $Q_\pi$ be the posterior distribution of $S$ given the transcript $\pi$. If $M$ is $(\varepsilon,\delta)$-differentially private, then for every query $\psi$ chosen as a function of the transcript, $\mathbb{E}_{S' \sim Q_\pi}[\psi(S')]$ (the empirical value of $\psi$ averaged over the posterior) is within $e^{\varepsilon} - 1 + O(\delta)$ of $\mathbb{E}_D[\psi]$ in expectation; and if $M$ is sample accurate, each answer is close to its posterior expectation with high probability, by a resampling thought experiment in which the dataset is redrawn from the posterior after the answers are fixed. Summing the two bounds gives the transfer theorem with substantially better constants than earlier monitor-based proofs.

## Proof sketch

Differential privacy bounds how much the transcript can shift the posterior on any single record, so the posterior mean of any linear statistic stays close to the prior mean, which is the population value. For the second part, conditioned on the transcript the true dataset is distributed as the posterior, so sample accuracy of the answer for the true dataset is the same event as accuracy for a fresh posterior sample, and concentration of linear statistics under the posterior completes the argument.

## Depends on

- [Differential privacy](../differential-privacy/differentially-private.md)

## Proof depends on

- [Transfer theorem for adaptive data analysis](../differential-privacy/differentially-private-transfer.md)
- [Differential privacy answers quadratically many adaptive statistical queries efficiently](adaptive-statistical-queries-via-privacy.md)

## Sources

- C. Jung, K. Ligett, S. Neel, A. Roth, S. Sharifi-Malvajerdi, M. Shenfeld, "A New Analysis of Differential Privacy's Generalization Guarantees", ITCS (2020), arXiv:1909.03577.
