# Transformer secret-recovery attack on LWE with sparse binary secrets

SALSA's attack on LWE with a sparse binary secret trains a sequence model to predict $b$ from $a$ on samples sharing the secret, turns the partly trained model into candidate secrets by direct and distinguisher-based recovery, and checks candidates by the spread of residuals. Success is empirical; no security reduction is claimed.

Fix LWE parameters $(n,q)$, an error distribution of small standard deviation $\sigma$, and a binary secret $s$ of small Hamming weight. The attack of Wenger, Chen, Charton and Lauter assumes access to many samples $(a,b)$ with $b=a\cdot s+e \bmod q$ and the same secret, and iterates the following.

1. **Training.** Train a sequence-to-sequence transformer $M$ to predict $b$ from $a$, with integers in $[0,q)$ written as digit sequences in a base $B$, by minimising cross-entropy over the output tokens. Model quality is the accuracy within tolerance $\tau$, $\mathrm{acc}_\tau$: the fraction of test samples with $|b-M(a)|\le\tau q$, computed on these integer representatives ($\tau=0.1$).
2. **Direct recovery**: SALSA's variant of direct secret recovery (SALSA, Algorithm 1). For ten integer values $K$ (five fixed, five random in $(q,10q)$), evaluate $p_i=M(Ke_i)$ for every standard basis vector $e_i$ and binarize $(p_1,\dots,p_n)$ by thresholding at the mean, at the mean after a softmax, or at the mode, in both orientations.
3. **Distinguisher recovery** (SALSA, Algorithm 2), run when $\mathrm{acc}_\tau$ exceeds a configured level ($30\%$), with a batch size $t$ taken as an input (the pseudocode derives it from $\mathrm{adv}$ below, capped at $50$). Put $\mathrm{adv}=\mathrm{acc}_\tau-2\tau$ and $\mathrm{bound}=\tau q$, draw $t$ LWE samples $(a_j,b_j)$, and initialise $s=0$. For each coordinate $i$: draw $t$ uniform pairs $(a^u_j,b^u_j)$ and $t$ uniform values $c_j$; let $a'_j$ be $a_j$ with $c_j$ added to its $i$-th coordinate modulo $q$; let $c_{\mathrm{LWE}}=\#\{j:|M(a'_j)-b_j|<\mathrm{bound}\}$ and $c_{\mathrm{unif}}=\#\{j:|M(a^u_j)-b^u_j|<\mathrm{bound}\}$; set $s_i=1$ if $c_{\mathrm{LWE}}-c_{\mathrm{unif}}\le\mathrm{adv}\cdot t/2$.
4. **Verification** (SALSA, Section 4.4), by the spread of residuals as in the residual test, with residuals of the opposite sign. For each candidate $\tilde s$, compute the residuals $a\cdot\tilde s-b \bmod q$ on a set of LWE samples; accept if their standard deviation is close to $\sigma$ rather than to $q/\sqrt{12}$ (about $3$ versus $72.5$ for $q=251$, $\sigma=3$). SALSA gives no numeric threshold and specifies neither the integer representatives of the residuals nor whether the samples are fresh.

In the source's experiments, candidates were compared with the known secret to decide success. With $q=251$, discrete Gaussian error of standard deviation $3$, and samples from the ring variant of LWE (each $a$ a row of a structured circulant matrix), Table 2 reports full secret recovery at the tested dimensions $n\in\{30,32,50,64,70,90,110,128\}$, with the highest density recovered at each; the text summarises this as Hamming weight $3$ for dimensions up to $128$ and weight $4$ for $n<70$. These are experimental results for those parameters.

## Remarks

This page asserts no correctness guarantee or running-time bound for the procedure: whether training reaches a model from which recovery succeeds is an empirical question. The source says only that verification uses "a set of LWE samples"; if those samples overlap the training samples, the candidates depend on them, and the exact residual laws of a fixed-candidate test on fresh samples do not apply directly. The pseudocode describes columns of $A$ as samples while indexing the $i$-th column of $A$; the reading above, which shifts the $i$-th coordinate of each sample, is the dimension-consistent one and matches the prose $a'_i=a_i+c$. Later papers in the same line add lattice-reduction preprocessing of the samples (SALSA PICANTE, SALSA VERDE) and replace the recovery rules (PICANTE compares $M(a+Ke_i)$ with $M(a)$ instead of with the label); those are separate procedures.

## Depends on

- [LWE with a prescribed secret distribution](../small-and-sparse-secret-lwe/lwe-with-a-secret-distribution.md)
- [Direct secret recovery from a trained LWE model](direct-secret-recovery.md)
- [Residual test for LWE secret candidates](residual-test-for-lwe-secret-candidates.md)
- [Gaussian function, Gaussian mass and discrete Gaussian on a lattice](../lattice-gaussians-and-smoothing-parameter/discrete-gaussian-on-a-lattice.md)

## Proof depends on

None.

## Sources

- Emily Wenger, Mingjie Chen, François Charton, Kristin Lauter, "SALSA: Attacking Lattice Cryptography with Transformers", Advances in Neural Information Processing Systems 35 (NeurIPS 2022); numbers from arXiv:2207.04785v2, Sections 4.1–4.4, Algorithms 1 and 2, Appendices C.1–C.2, Section 5.1 and Table 2.
