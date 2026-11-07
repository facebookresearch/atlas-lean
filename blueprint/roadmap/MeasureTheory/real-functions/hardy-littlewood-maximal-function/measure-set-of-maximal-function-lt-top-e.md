# The maximal function of a singular measure is infinite almost everywhere for that measure

**The maximal function of a singular measure is infinite almost everywhere for that
measure.** Let $n$ be a natural number and let $\mu$ be a Borel measure on $\mathbb{R}^n$ that is
mutually singular with respect to Lebesgue measure $m_n$. Write $B(x, r)$ for the open ball of
radius $r$ about $x$ and define $M_\mu : \mathbb{R}^n \to [0, \infty]$ by

$$
M_\mu(x) = \sup_{r>0} \frac{\mu(B(x, r))}{m_n(B(x, r))}.
$$

Then $\mu(\{x \in \mathbb{R}^n : M_\mu(x) < \infty\}) = 0$.

## Sources

- MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Measure and integration; Classical measure theory), `benchmark/level2/ma_proofbench_l2_44.lean` at openbmb/ma-proofbench@31bab4c.
