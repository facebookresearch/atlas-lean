# The Blum–Kalai–Wasserman algorithm for learning parity with noise

For every constant noise rate $\eta<1/2$, parities on $\{0,1\}^k$ under the uniform distribution with random classification noise can be learned with $2^{O(k/\log k)}$ examples and time, by cancelling blocks of coordinates so that a basis vector becomes a sum of few examples, without looking at their labels.

In the *length-$k$ parity problem* with noise rate $\eta\in[0,1/2)$, each example $(x,\ell)$ has $x$ uniform in $\{0,1\}^k$ and $\ell=x\cdot c \bmod 2$ flipped independently with probability $\eta$, for an unknown $c\in\{0,1\}^k$; examples are independent.

**Theorem.** For every constant $\eta<1/2$ there is an algorithm that, using $2^{O(k/\log k)}$ examples and total time $2^{O(k/\log k)}$, outputs $c$ except with probability exponentially small in $k$.

**Noise accumulation.** If $(x_1,\ell_1),\dots,(x_s,\ell_s)$ are noisy examples, then $\ell_1+\dots+\ell_s=(x_1+\dots+x_s)\cdot c$ with probability $\frac12+\frac12(1-2\eta)^s$.

**One batch.** Let $a=\max(1,\lceil\frac12\log_2k\rceil)$ and $b=\lceil k/a\rceil$ (the source takes $a=\frac12\log_2k$, $b=2k/\log_2k$), and split the $k$ coordinates into $a$ consecutive blocks of sizes $b_1,\dots,b_a$ with $1\le b_j\le b$; examples stay uniform on $\{0,1\}^k$. Let $V_i$ be the vectors whose last $i$ blocks vanish; an *$i$-sample of size $t$* is a set of $t$ vectors independent and uniform on $V_i$. Draw $a2^b$ fresh examples (a $0$-sample) and apply $a-1$ times the step: partition the current vectors by their values on the next block to be eliminated; in each nonempty class choose one vector uniformly at random, using fresh coins independent of everything else, add it to each of the other vectors of the class, and discard it. Each step turns an $i$-sample of size $t$ into an $(i+1)$-sample of size at least $t-2^b$, so the result is an $(a-1)$-sample of size at least $2^b$, each vector being the sum of at most $2^{a-1}$ original examples, formed without examining labels. The batch is a *hit* if $(1,0,\dots,0)$ occurs among these vectors; since $V_{a-1}$ has $2^{b_1}\le2^b$ elements, a batch is a hit with probability at least $1-(1-2^{-b_1})^{2^b}\ge1-1/e$. A hit yields one estimate of $c_1$, the sum of the labels of one such vector, correct with probability at least $p_0=\frac12+\frac12(1-2\eta)^{2^{a-1}}$.

**Budget.** Put $\delta=p_0-\frac12$ and $T=\lceil k/\delta^2\rceil$. Run $R=4T$ independent batches; if fewer than $T$ are hits, output an arbitrary guess (failure); otherwise take the majority of the estimates from the first $T$ hits as $c_1$. Cyclic shifts of the coordinates give the other bits.

## Proof sketch

Noise accumulation is the piling-up lemma for $s$ independent error bits: $\frac12+2^{s-1}(\frac12-\eta)^s$. Elimination step (Lemma 4): the class of a vector is determined by its eliminated block, and the representative is chosen uniformly by fresh coins; adding it to another vector of the class zeroes that block, and conditionally on the representative the other vectors of the class are independent and uniform on the vectors of $V_i$ agreeing with it on that block, so their sums are independent and uniform on $V_{i+1}$. The selected vector's label error is the sum of the noise bits of its at most $2^{a-1}$ contributing examples (an example used twice cancels), independent of all feature vectors because labels are never examined, so its estimate is correct with probability at least $p_0$.

Failure events. The hit indicators of the $R$ batches are independent with a common mean $p_{\mathrm{hit}}\ge1-1/e>0.63$, so $Rp_{\mathrm{hit}}-T\ge0.38R$ and, by Hoeffding's inequality for Bernoulli sums, fewer than $T$ hits (which forces $|S_{\mathrm{hit}}-Rp_{\mathrm{hit}}|>0.38R$) occur with probability at most $2e^{-2(0.38)^2R}\le2e^{-k}$, because $R=4T\ge16k$. Given at least $T$ hits, the correctness indicators of the first $T$ estimates are independent with a common mean $p\ge p_0$ (one estimate per batch, because labels within a batch are correlated), and at most half correct forces $Tp-S\ge T\delta>T\delta/2$ for the number $S$ of correct estimates, so Hoeffding's inequality bounds this probability by $2e^{-2(\delta/2)^2T}\le2e^{-k/2}$. A union bound over the $k$ bits gives failure probability at most $4ke^{-k/2}$. Cost: $k\cdot4T\cdot a2^b$ examples and comparable time, with $2^b=2^{O(k/\log k)}$ and $\delta^{-2}=4(1-2\eta)^{-2^{a}}\le4(1-2\eta)^{-2\sqrt k}=2^{O(\sqrt k)}$, since $2^a\le2\sqrt k$ for $k\ge2$; the total is $2^{O(k/\log k)}$. For $k=1$ the definition gives $a=b=1$, there is no elimination step, and a batch of two examples is a hit unless both have $x=0$. Consequence: for $k=O(\log n\log\log n)$ the running time is polynomial in $n$, so parities on the first $O(\log n\log\log n)$ bits are learnable with random classification noise although they are not learnable in Kearns's statistical query model.

## Depends on

- [Learning parity with noise](../../cryptography/public-key/lattice-and-code-based-cryptography/lattice-gaussians-and-smoothing-parameter/learning-parity-with-noise.md)

## Proof depends on

- [Piling-up lemma](../../cryptography/symmetric-key/piling-up-lemma-and-toy-substitution-permutation/piling-up.md)
- [Two-sided Hoeffding inequality for Bernoulli sums](../../../Probability/concentration-inequalities/hoeffding-s-inequality/hoeffding-bernoulli-sum-abs-tail.md)

## Sources

- Avrim Blum, Adam Kalai, Hal Wasserman, "Noise-tolerant learning, the parity problem, and the statistical query model", Journal of the ACM 50(4):506–519, 2003; numbers from the preprint arXiv:cs/0010022v1: Section 3.1, Theorem 2, Lemma 3, Definition 2 and Lemma 4, and Section 2 for the statistical-query consequence.
