# Round-by-round soundness of FRI

Consider smooth FRI with arities $l^{(i)} = 2^{s_i}$, domain size $2^d$, initial rate $\rho$, distance threshold $e$, and $q$ query repetitions. Declare a prefix doomed when the current oracle is $e$-far (in Hamming weight relative to the current domain) from the current Reed–Solomon code. Then FRI is round-by-round sound: (i) in the unique-decoding regime $2e + \dim_0 \le 2^d$, round $i$ escapes with probability at most $(l^{(i)} - 1)\, n_{i+1}/|\mathbb{F}|$, and these budgets telescope, $\sum_i (l^{(i)} - 1) n_{i+1} = 2^d - 2^{d - \sum_i s_i}$; (ii) in the Johnson regime $e/2^d \le 1 - \sqrt{\rho} - \sqrt{\rho}/(2m)$ the escape probabilities are bounded by the Johnson-regime proximity-gap bound; (iii) once all rounds are doomed, a single query passes with probability at most $1 - e/2^d$, so $q$ independent queries pass with probability at most $(1 - e/2^d)^q$. Hence the interactive soundness error of FRI is at most the sum of the commit-phase escape bounds plus $(1 - e/2^d)^q$; the same holds for batched FRI with an additional round-$0$ term from batching.

## Proof sketch

The commit-phase bound is the proximity-gap theorem applied to the fiber components of a far word: if the fold were close for too many challenges, the word itself would be close. The query bound counts starting points: from a doomed final prefix, every inconsistency on a fiber propagates, and the fraction of starting points passing all consistency checks is at most $1 - e/2^d$.

## Depends on

- [The FRI protocol](fri-protocol.md)
- [Public-coin interactive oracle proofs](../interactive-oracle-proofs/public-coin-iop.md)

## Proof depends on

- [Proximity gaps and correlated agreement for Reed–Solomon codes](reed-solomon-proximity-gaps.md)
- [Prefix union bound for round-by-round sound IOPs](../interactive-oracle-proofs/iop-prefix-union-bound.md)

## Sources

- Eli Ben-Sasson, Iddo Bentov, Yinon Horesh and Michael Riabzev, "Fast Reed–Solomon Interactive Oracle Proofs of Proximity", 45th International Colloquium on Automata, Languages, and Programming (ICALP 2018), 2018.
- Eli Ben-Sasson et al., "Proximity Gaps for Reed–Solomon Codes", Journal of the ACM, 2023.
