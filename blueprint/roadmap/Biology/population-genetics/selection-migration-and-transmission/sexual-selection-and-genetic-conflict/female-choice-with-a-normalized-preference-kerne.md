# Female choice, parental contributions and mating fertility

Let $I,K$ be finite nonempty sets of male trait and female preference
types, with probability vectors $q_i,r_k$. Let $\psi_k(i)>0$ and suppose
each female mates once, choosing a male independently with probability

$$P_k(i)=\frac{q_i\psi_k(i)}{\sum_jq_j\psi_k(j)}.$$

Suppose male availability imposes no capacity constraint and every mating
has the same positive expected offspring contribution. The joint
parent-type law among offspring is $J_{ki}=r_kP_k(i)$.
Its maternal marginal is $r_k$, and its paternal marginal is

$$q_i^{\rm pat}=\sum_kr_kP_k(i),\qquad\sum_iq_i^{\rm pat}=1.$$

If $\psi_k$ is constant in $i$ for each $k$, then $J_{ki}=r_kq_i$ and
$q^{\rm pat}=q$. If all females share a kernel $\psi$, the paternal
marginal is the [haploid selection map](../../natural-selection-fisher-s-theorem-and-the-price/select.md)
$q_i\psi(i)/\sum_jq_j\psi(j)$.
These are parental contributions, not automatically the next generation's
trait or preference frequencies; that requires an inheritance model.

More generally let a pair $(k,i)$ have nonnegative expected fertility
$F_{ki}$ and let $\bar F=\sum_{ki}r_kP_k(i)F_{ki}>0$. Then the offspring's
parent-pair law is $J^F_{ki}=r_kP_k(i)F_{ki}/\bar F$.
Its maternal marginal is
$r_k\sum_iP_k(i)F_{ki}/\bar F$, and its paternal marginal is
$\sum_kr_kP_k(i)F_{ki}/\bar F$.
Thus fertility differences can change either marginal; the maternal
marginal is unchanged exactly when each preference type of positive
frequency has the same conditional mean fertility $\bar F$.

## Depends on

- [Selection map](../../natural-selection-fisher-s-theorem-and-the-price/select.md)

## Expansion

Positivity and the probability-vector hypotheses make each normalization
finite and positive. Sum $P_k(i)$ over $i$, then sum $J$ or $J^F$ over the
appropriate index. This proves normalization and both marginal formulas.
The neutral and common-kernel specializations follow by cancellation.
Fertility depends on the completed mating, so weighting by $F$ occurs
after the mate-choice probabilities are normalized.

## Sources

- R. Lande, "Models of speciation by sexual selection on polygenic traits", PNAS 78 (1981), 3721--3725, <https://doi.org/10.1073/pnas.78.6.3721>, abstract, for male genetic contribution and female choice among potential mates. The finite kernel and fertility-weighting model are explicitly derived here, not claimed to reproduce the full polygenic model.
