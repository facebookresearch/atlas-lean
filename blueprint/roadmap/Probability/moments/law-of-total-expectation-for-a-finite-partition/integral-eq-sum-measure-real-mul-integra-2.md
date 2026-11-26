# Law of total expectation

On a finite measure space, let $B_1, \dots, B_m$ be finitely many measurable, pairwise disjoint sets covering the whole space, and let $f$ be integrable. Then $\int f \, d\mu = \sum_i \mu(B_i)\, \mathbb{E}[f \mid B_i]$, where $\mathbb{E}[f \mid B_i]$ is the integral of $f$ against $\mu$ conditioned on $B_i$ (the zero measure, hence integral $0$, when $\mu(B_i) = 0$).
