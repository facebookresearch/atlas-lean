# Unbiased high-dimensional predictions give downstream decision makers no swap regret

Consider sequential prediction of an adversarially chosen state $s_t$ in a convex compact set $C \subseteq \mathbb{R}^d$ by a randomized forecast $\hat s_t \sim \psi_t$, required to be unbiased conditional on every event $E$ in a family $\mathcal{E}$ of conditioning events (functions of the context, the history and the forecast, with values in $[0,1]$): $\big|\mathbb{E}\sum_{t \le T} E(x_t, \hat s_t)\,(\hat s_{t,i} - s_{t,i})\big|$ small for every $E \in \mathcal{E}$ and coordinate $i$. There is an algorithm achieving bias $O\big(\ln(2d|\mathcal{E}|T) + \sqrt{\ln(2d|\mathcal{E}|T)\,\sum_t \mathbb{E}[E(x_t, \hat s_t)^2]}\big)$, with per-round time polynomial in $d$, $|\mathcal{E}|$ and the cost of evaluating the events. Choosing $\mathcal{E}$ to consist of the best-response regions $\{\hat s : a \text{ is a best response to } \hat s \text{ under } u\}$ of polynomially many downstream decision makers with $K$ actions and utilities $u(a, s)$ that are linear and $L$-Lipschitz in the state, each decision maker who best responds to the forecasts as if they were correct has swap regret at most $2LK\,\alpha(T/K)/T$, where $\alpha(n)$ is the (concave) bias bound for an event occurring $n$ times, which is the optimal $\tilde O(\sqrt{K/T})$ rate, simultaneously; the construction extends to large combinatorial action spaces, to extensive-form games, and to online multiclass prediction sets with multigroup coverage.

## Proof sketch

Unbiasedness conditioned on the event "decision maker $i$ best-responds with action $a$" says that, on the rounds where $i$ plays $a$, the average realized state equals the average forecast, so any swap $a \mapsto a'$ gains at most the conditional bias times the utility's Lipschitz constant. The unbiased predictions themselves are obtained by a reduction to a minimax problem in each round: an experts algorithm (the multi-scale multiplicative weights with correction of Chen, Luo and Wei) maintains weights over (coordinate, sign, event) triples measuring the cumulative biases, and the forecaster solves for a distribution over forecasts that is a near-equilibrium of the resulting zero-sum game, which exists by the minimax theorem.

## Depends on

- [Swap regret](../../../GameTheory/not-yet-classified/part-02/regret/swap-regret.md)

## Sources

- G. Noarov, R. Ramalingam, A. Roth, S. Xie, "High-Dimensional Prediction for Sequential Decision Making", ICML (2025), arXiv:2310.17651, Theorems 3.1 and 4.1.
