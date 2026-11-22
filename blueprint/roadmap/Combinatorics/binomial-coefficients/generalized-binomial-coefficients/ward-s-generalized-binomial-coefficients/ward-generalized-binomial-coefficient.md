# Ward generalized binomial coefficient

Let $R$ be a commutative monoid and
$s = (s_b)_{b \in \mathbb{N}}$ a sequence in $R$. For natural numbers $n$ and $m$, the Ward
generalized binomial coefficient is

$$\binom{n+m}{n}_s = \prod_{b=2}^{n+m} s_b^{\varepsilon_0^{b,n,m}},$$

where $\varepsilon_0^{b,n,m} \in \{0, 1\}$ is the carry in the units place when $n$ and $m$ are
added in base $b$.

This is Ward's product $\prod_{b > 1} s_b^{\varepsilon_0^{b,n,m}}$: no base larger than $n + m$
carries in the units place, so the product is finite. The source uses the product as a
definition for arbitrary coefficient sequences, including sequences with zero terms.
