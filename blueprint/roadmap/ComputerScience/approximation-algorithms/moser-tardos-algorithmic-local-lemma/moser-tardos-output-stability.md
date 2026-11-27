# Coupled Moser-Tardos runs and stability of the output law in total variation

Consider two Moser-Tardos runs on the same events, with variable laws $P_v$ and $Q_v$, driven by a table whose entries are independent pairs drawn from couplings of $P_v$ and $Q_v$ that disagree with probability $\eta_v$, and with a non-anticipating selection rule (one that sees only the log and the current assignment). Let $N_v$ be the number of samples of $v$ read by the first run. Then

$$
\Pr[\text{the runs diverge}] \le \sum_v \eta_v\, \mathbb{E}[N_v],
$$

and under the local-lemma hypothesis for $(P_v)$, $\mathbb{E}[N_v] \le 1 + \sum_{i : v \in \mathrm{vbl}(A_i)} x_i/(1-x_i)$. In the symmetric case $e\,q\,(d+1) \le 1$ at most $d + 1$ events contain $v$, so $\mathbb{E}[N_v] \le 1 + (d+1)/d \le 3$ for $d \ge 1$ (and $\mathbb{E}[N_v] \le 1 + 1/(e-1) < 2$ for $d = 0$), which gives divergence probability at most $3\sum_v \eta_v$; with optimal couplings the output laws satisfy $d_{TV}(\mathrm{MT}(P), \mathrm{MT}(Q)) \le 3\sum_v d_{TV}(P_v, Q_v)$, and with distribution-independent correlated sampling (each run knowing only its own laws) both runs output the same good assignment except with probability $6\sum_v d_{TV}(P_v, Q_v)$.

## Proof sketch

Two runs stay identical while every table entry read by the first run is an agreeing pair. Whether the first run ever reads entry $(v,k)$ does not depend on that entry, so a union bound over entries actually read gives $\sum_v \eta_v \mathbb{E}[N_v]$. The local-lemma bound on resamplings bounds $\mathbb{E}[N_v]$, and the coupling inequality converts divergence into total variation of outputs; Holenstein's correlated sampling disagrees with probability at most twice the total variation.

## Depends on

- [Moser-Tardos resampling algorithm in the variable model](moser-tardos-algorithm.md)
- [Total variation distance between finite measures](../../../Probability/convergence-of-measures/total-variation-distance/total-variation-dist.md)

## Proof depends on

- [Moser-Tardos theorem: the resampling algorithm finds an assignment avoiding all events](moser-tardos-theorem.md)
- [Symmetric Moser-Tardos bound: e q (d+1) <= 1](symmetric-moser-tardos.md)
- [Coupling of two probability measures](../../../MeasureTheory/optimal-transport/kantorovich-duality/is-coupling.md)

## Sources

- Robin A. Moser and Gábor Tardos, "A Constructive Proof of the General Lovász Local Lemma", Journal of the ACM 57(2), 2010.
- Thomas Holenstein, "Parallel Repetition: Simplifications and the No-Signaling Case", Theory of Computing 5, 2009.
