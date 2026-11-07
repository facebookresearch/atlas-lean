# A strict liminf gap at every finite value forces countably many finite values

Let
$f : [0,1] \to [0,\infty]$ be such that for every $y \in [0,1]$ with $f(y) \ne \infty$,

$$
\liminf_{x \to y,\ x \ne y} f(x) > f(y),
$$

where $x$ ranges over $[0,1]$. Then the set $\{y\in[0,1] : f(y) < \infty\}$ is countable.

## Sources

- MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Real functions; Functions of one variable), `benchmark/level2/ma_proofbench_l2_32.lean` at openbmb/ma-proofbench@31bab4c.
