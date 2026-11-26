# Coefficient and truncation bounds for a simultaneous-root sieve

For a natural squarefree modulus $P>1$, define the normalizer, the divisor coefficients and the tilted absolute moment by

$$
B(P)=\sum_{\substack{d\mid P\\d>1}}\frac1{\varphi(d)\log d},\qquad
a_P(1)=1,\quad a_P(d)=-\frac1{B(P)\log d}\ (d>1,\ d\mid P),\qquad
A_P(\gamma)=\sum_{\substack{d\mid P\\d>1}}\frac{|a_P(d)|d^\gamma}{\varphi(d)}.
$$

## Finite sieve hypotheses

The coefficient hypotheses for parameters $P,\beta,C$ are that $P>1$ is squarefree, every divisor coefficient satisfies $|a_P(d)|\le 1$, and for every real tilt $0\le\gamma\le2\beta$,

$$ A_P(\gamma)\le C,\qquad A_P(\gamma)\le C B(P). $$

These are assumptions of the finite weighted sieve, not conclusions for an arbitrary squarefree modulus. For example, at a prime modulus $P=p$ one has $A_p(0)=1$ while $B(p)=1/((p-1)\log p)$.

For $m\ge1$ root indices, the finite argument assumes $\beta\ge0$, a product cutoff $D\ge1$, an integer prime lower bound $M>1$ with every prime divisor of $P$ strictly larger than $M$, and an averaging interval of integer length $T>0$. At each prime divisor the $m$ prescribed residues must be pairwise distinct. The separate small-loss bounds concern the diagonal mass, the Gram factor, the interval error and the sum of the uncovered-root moments. In particular the Gram factor is $\exp(m\log D/((M-1)\log M))$ and the interval error term is $16D^6/T$.

## Expansion

State the exact truncated root weights and their replacements, the diagonal mass and collision loss, and the finite weighted-sieve lemma for arbitrary injective residue families **under** the coefficient and small-loss hypotheses. Keep all assumptions explicit and all finite bounds uniform in the allowed tilt and number of roots. The auxiliary-prime estimates used to specialize the finite lemma are a separate result.

## Sources

- [Normalizer and coefficients](https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L49-L55)
- [Tilted absolute moment](https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L175-L177)
- [Coefficient estimate hypotheses](https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1790-L1802)
- [Finite simultaneous-root lemma and small-loss hypotheses](https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L3253-L3263)
