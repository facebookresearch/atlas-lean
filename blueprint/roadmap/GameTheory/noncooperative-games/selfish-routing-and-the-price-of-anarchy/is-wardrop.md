# Wardrop equilibrium

A path flow $f$ is a Wardrop equilibrium (a flow at Nash equilibrium) if for all paths
$P_1, P_2$ of the same commodity with $f_{P_1} > 0$, $\ell_{P_1}(f) \le \ell_{P_2}(f)$: every path
carrying flow has minimum latency among the paths of its commodity. In particular all flow
paths of a commodity have the same latency.

Roughgarden and Tardos define flows at Nash equilibrium by infinitesimal deviations
(Definition 2.1) and prove that for continuous nondecreasing latencies this is equivalent to the
condition above (Lemma 2.2). The definition here is the condition itself, for arbitrary
latencies.

## Sources

- T. Roughgarden and É. Tardos, "How bad is selfish routing?", J. ACM 49(2) (2002), 236–259, Definition 2.1 and Lemma 2.2.
- J. G. Wardrop, "Some theoretical aspects of road traffic research", Proc. Inst. Civil Engineers
  1 (1952), 325–378.
