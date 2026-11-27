# Symmetric Moser-Tardos bound: e q (d+1) <= 1

In the variable model, suppose every event has probability at most $q$ and shares variables with at most $d$ other events, and $e\,q\,(d+1) \le 1$. Then for every valid selection rule the algorithm stops almost surely at an assignment avoiding every event (when the rule stops only at such assignments), and the expected number of resamplings of each event is at most $1/d$ when $d \ge 1$, and at most $q/(1-q) \le 1/(e-1)$ when $d = 0$.

## Proof sketch

Take $x_i = 1/(d+1)$ when $d \ge 1$; then $x_i\prod_{j\in\Gamma(i)}(1-x_j) \ge \frac{1}{d+1}(1 - \frac1{d+1})^d \ge \frac{1}{e(d+1)} \ge q$, and $x_i/(1-x_i) = 1/d$. For $d = 0$ take $x_i = \Pr[A_i]$. Apply the Moser-Tardos theorem.

## Depends on

- [Moser-Tardos resampling algorithm in the variable model](moser-tardos-algorithm.md)
- [Symmetric Lovász Local Lemma](../../../Combinatorics/probabilistic-combinatorics/lovasz-local-lemma-symmetric-finite.md)

## Proof depends on

- [Moser-Tardos theorem: the resampling algorithm finds an assignment avoiding all events](moser-tardos-theorem.md)

## Sources

- Robin A. Moser and Gábor Tardos, "A Constructive Proof of the General Lovász Local Lemma", Journal of the ACM 57(2), 2010.
