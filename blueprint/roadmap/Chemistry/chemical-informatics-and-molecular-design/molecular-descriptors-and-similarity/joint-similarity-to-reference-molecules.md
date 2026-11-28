# Joint similarity to several reference molecules

A molecule that resembles one reference closely and the others not at all should not score as a good compromise. Joint similarity takes the mean similarity to the references and subtracts the spread between the largest and the smallest of them.

Let $M = \{m_1, \dots, m_n\}$, $n = |M| \ge 1$, be reference molecules and let $\mathrm{sim}(m_i, m) \in [0,1]$ be supplied similarity values between each reference and a candidate $m$. The joint similarity is

$$
F(m) = \frac{1}{n} \sum_{i=1}^{n} \mathrm{sim}(m_i, m) - \Big[ \max_{i} \big(\mathrm{sim}(m_i, m)\big) - \min_{i} \big(\mathrm{sim}(m_i, m)\big) \Big] .
$$

A *median molecule* of $M$, relative to a nonempty finite set of candidates, is a candidate maximizing $F$ over that set.

For $n = 1$ the bracket vanishes and $F(m) = \mathrm{sim}(m_1, m)$. For $n \ge 2$, $F(m) \le \frac{1}{n}\sum_i \mathrm{sim}(m_i,m) \le 1$, with equality in the first bound exactly when all similarities coincide, and $F(m) \ge -1$; values such as $-1/2$ occur, for similarities $1$ and $0$. Negative values are intended: a candidate similar to one reference only scores below a uniformly mediocre candidate, which is the behaviour the geometric mean of similarities lacks.

The score is defined on supplied similarity values and commits to no fingerprint; a computation on molecules fixes a fingerprint and a similarity, which the source takes to be a Tanimoto similarity of circular fingerprints, and a finite candidate set, without which a maximizer need not exist.

## Depends on

None.

## Proof depends on

None.

## Expansion

A formal development takes a nonempty finite index type, similarity values in $[0,1]$, and defines $F$ by the display with the finite maximum and minimum. The bounds follow from $0 \le \min_i \le \frac{1}{n}\sum_i \le \max_i \le 1$, and the equality case from the equality case of that chain. Existence of a maximizer is the finite-nonempty-set argument and is stated with the candidate set, not with the score.

## Context

Graduate. The scoring function Nigam, Pollice, Krenn, dos Passos Gomes and Aspuru-Guzik introduce for median molecules, reused as the selection pressure of the exploitative population in their later genetic algorithm.

## Sources

- AkshatKumar Nigam, Robert Pollice, Mario Krenn, Gabriel dos Passos Gomes and Alán Aspuru-Guzik, *Beyond generative models: superfast traversal, optimization, novelty, exploration and discovery (STONED) algorithm for molecules using SELFIES*, Chemical Science 12 (2021) 7079–7090, Section II C, Eq. 1. DOI [10.1039/d1sc00231g](https://doi.org/10.1039/d1sc00231g), PMC8153210.
- AkshatKumar Nigam, Robert Pollice and Alán Aspuru-Guzik, *Parallel tempered genetic algorithm guided by deep neural networks for inverse molecular design*, Digital Discovery 1 (2022) 390–404, Eq. 2. DOI [10.1039/d2dd00003b](https://doi.org/10.1039/d2dd00003b), PMC9358752.
