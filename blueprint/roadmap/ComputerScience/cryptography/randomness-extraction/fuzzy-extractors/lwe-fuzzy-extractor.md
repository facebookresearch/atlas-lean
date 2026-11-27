# A computational fuzzy extractor from LWE (decode-then-extract)

Let $q$ be prime and $n = k + l$. Over the Hamming space $\mathbb{Z}_q^m$ with $m \ge n$, let $\mathrm{Gen}(w)$ sample a uniform matrix $A \in \mathbb{Z}_q^{m \times n}$ and a uniform secret $s \in \mathbb{Z}_q^n$, publish $p = (A, As + w)$ and output the first $k$ coordinates of $s$ as the key; $\mathrm{Rep}(w', p)$ subtracts $w'$ and decodes the resulting LWE sample $As + (w - w')$, whose error $w - w'$ has Hamming weight at most $t$. *Security*: if decision LWE in dimension $l$ with $m$ samples holds with the source distribution of the reading $w$ as the error distribution, then $(s_{1..k}, p)$ is computationally indistinguishable from $(U, p)$ (Fuller, Meng and Reyzin, Lemma 4.7). *Correctness*: if moreover $m \ge 3n$ and $t \le d\,(m/n - 2)\log n$ for a constant $d > 0$, the decoder that repeatedly picks $2n$ random rows, solves the system on $n$ linearly independent ones among them and accepts a solution $x'$ once $As + (w - w') - Ax'$ has at most $t$ nonzero coordinates returns $s$ with probability $1 - e^{-\Omega(n)}$ over $A$ and its coins, in expected $O(n^{4d+3})$ operations over $\mathbb{Z}_q$ (Construction 4.9 and Lemma 4.10). Under these conditions the scheme is a computationally secure fuzzy extractor with error $e^{-\Omega(n)}$, rather than a perfectly correct one, and some bound on $t$ is necessary: for $t = m$, correctness would let anyone compute the key from $p$ and a fixed $w'$, contradicting security. Theorem 4.11 gives one such parameter setting, with $t = c\log n$ and a uniform source over a small alphabet.

## Proof sketch

The helper is an LWE sample with the reading as error. Hybrid: replace $As_{k+1..} + w$ by uniform using LWE in dimension $l$ (treating the key part as a known shift), after which the key coordinates are masked by uniform columns and hence independent of the helper. Correctness: with probability at least $1/\mathrm{poly}(n)$ the $2n$ chosen rows avoid every error, and the random code spanned by $A$ has distance at least $2t + 1$ except with probability $e^{-\Omega(n)}$, so a wrong candidate is always rejected.

## Depends on

- [Fuzzy extractor and secure sketch](fuzzy-extractor.md)
- [Learning with errors](../../public-key/hardness-assumptions/learning-with-errors.md)

## Sources

- B. Fuller, X. Meng and L. Reyzin, "Computational Fuzzy Extractors", Information and Computation 275, 2020, Construction 4.1, Lemma 4.7, Construction 4.9, Lemma 4.10 and Theorem 4.11.
