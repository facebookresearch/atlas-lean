# Replicable constraint solving by the Moser-Tardos algorithm

Let finitely many variables $v$ take values in finite sets, let finitely many bad events $(E_j)_{j \in \iota}$ each depend on a set of variables, with dependency graph $\Gamma$, and let a learner estimate from a dataset $S$ distributions $\hat P_S(v)$ on the variables with a common denominator $L$. Run a non-anticipating Moser-Tardos resampling rule, which only selects occurring events and stops only when none occurs, for at most $B$ steps, reading resampled values from a table generated from a shared seed by correlated sampling (each table entry drawn from $\hat P_S(v)$ via a shared uniform enumeration), and output $\mathrm{none}$ on timeout. Suppose that for every dataset in a set $\mathrm{good}$, every event has at most $d$ neighbours in $\Gamma$ and probability at most $p$ under the product of the $\hat P_S(v)$, with $e\,p\,(d+1) \le 1$. Then:

1. two runs on independent $m$-samples from $D$ sharing the seed disagree with probability at most $4\sum_v \mathbb{E}_{S,S'}\, d_{TV}(\hat P_S(v), \hat P_{S'}(v)) + \Pr[S \notin \mathrm{good}]$, for every budget $B$;
2. a run fails to output an assignment avoiding every event with probability at most $|\iota|/((d+1)(B+1)) + \Pr[S \notin \mathrm{good}]$.

## Proof sketch

Correlated sampling from a shared enumeration makes two table entries drawn from $P$ and $Q$ differ with probability at most $2\,d_{TV}(P,Q)/(1 + d_{TV}(P,Q))$; for fixed estimates, a coupling of the two resampling runs shows they diverge only if some table entry read by one of them differs, giving the factor $4\sum_v d_{TV}$. the Moser-Tardos analysis bounds the expected number of resamplings by $|\iota|/(d+1)$ under the local lemma condition $e\,p\,(d+1) \le 1$, and Markov's inequality bounds the timeout probability.

## Depends on

- [Replicable algorithms with shared randomness](replicable-algorithms-with-shared-seed.md)
- [Lovász local lemma, general form](../../../../Combinatorics/probabilistic-combinatorics/lovasz-local-lemma-general-finite.md)
- [Total variation distance between finite measures](../../../../Probability/convergence-of-measures/total-variation-distance/total-variation-dist.md)

## Proof depends on

- [Lovász local lemma, general form](../../../../Combinatorics/probabilistic-combinatorics/lovasz-local-lemma-general-finite.md)

## Sources

- R. A. Moser and G. Tardos, "A Constructive Proof of the General Lovasz Local Lemma", Journal of the ACM, 2010.
- T. Holenstein, "Parallel Repetition: Simplifications and the No-Signaling Case", Theory of Computing, 2009.
- R. Impagliazzo, R. Lei, T. Pitassi and J. Sorrell, "Reproducibility in Learning", Proceedings of the 54th Annual ACM SIGACT Symposium on Theory of Computing (STOC), 2022.
