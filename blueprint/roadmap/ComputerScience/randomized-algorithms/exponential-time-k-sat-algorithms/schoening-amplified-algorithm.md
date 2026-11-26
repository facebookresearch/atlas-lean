# Schöning's algorithm on the randomized word RAM

Fix $k \ge 3$ and a confidence parameter $c \in \mathbb{N}$. There is a randomized word-RAM program that on input $(k, c, \varphi)$ runs at most $R = \lceil (3n+1)(2(k-1)/k)^n (k/(k-1))^{k-3} \rceil \cdot c$ independent Schöning trials, maintaining $R$ in a multiword counter, and

1. halts on every run within $O\big(R \cdot (n + L)\big)$ instructions, where $L$ is the input length, using at most $4nR$ random draws;
2. outputs $1$ only together with a satisfying assignment of $\varphi$ stored in memory, and otherwise outputs $0$;
3. if $\varphi$ is satisfiable, outputs $0$ with probability at most $e^{-c}$.

For $3$-SAT this decides satisfiability with one-sided error in time $(4/3)^n \cdot \mathrm{poly}(n, L)$.

## Proof sketch

Trials are independent, so the failure probability is $(1 - p_{k,n})^R \le e^{-p_{k,n} R} \le e^{-c}$ by the trial success bound and the choice of $R$.

## Depends on

- [Schöning's random-walk trial](schoening-random-walk-trial.md)
- [Randomized word RAM](../../sorting-and-searching/word-ram-integer-algorithms/randomized-word-ram.md)
- [Multiword counters on the word RAM](../../sorting-and-searching/word-ram-integer-algorithms/multiword-counter.md)
- [Exponential Time Hypothesis and Strong Exponential Time Hypothesis](../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/exponential-time-hypothesis-and-strong.md)

## Proof depends on

- [Success probability of one Schöning trial](schoening-trial-success-probability.md)
- [Multiword counters on the word RAM](../../sorting-and-searching/word-ram-integer-algorithms/multiword-counter.md)

## Sources

- U. Schöning, "A Probabilistic Algorithm for k-SAT and Constraint Satisfaction Problems", 40th IEEE Symposium on Foundations of Computer Science (FOCS), 1999.
