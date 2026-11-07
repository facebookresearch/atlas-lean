# Cauchy's formula for the twice-iterated integral

Let $E$ be a real Banach space, let
$\alpha \le \beta$ be real numbers and let $f : \mathbb{R} \to E$ be continuous on
$[\alpha, \beta]$. Then for every $s \in [\alpha, \beta]$,

$$\int_\alpha^s \Bigl(\int_\alpha^t f(\tau)\,d\tau\Bigr)\,dt = \int_\alpha^s (s - t)\, f(t)\,dt.$$

## Sources

- MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Real functions; Functions of one variable), `benchmark/level1/ma_proofbench_l1_44.lean` at openbmb/ma-proofbench@31bab4c.
