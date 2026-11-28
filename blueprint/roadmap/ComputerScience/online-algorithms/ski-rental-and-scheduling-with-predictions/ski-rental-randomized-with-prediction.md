# Randomized ski rental with a prediction

For every integer $b \ge 2$ and every $\lambda \in (1/b, 1)$, let $m = \lfloor \lambda b \rfloor$ if the prediction satisfies $y \ge b$ and $m = \lceil b/\lambda \rceil$ otherwise, and buy at the start of day $j \in \{1, \dots, m\}$ with probability proportional to $\left(\frac{b-1}{b}\right)^{m-j}$. Against an oblivious adversary, this randomized ski-rental algorithm has expected competitive ratio at most $\frac{\lambda}{1 - e^{-\lambda}}\left(1 + \frac{\eta}{\mathrm{OPT}}\right)$; in particular it is $\frac{\lambda}{1 - e^{-\lambda}}$-consistent, a value that tends to $1$ as $\lambda \to 0$ and to the optimal randomized ratio $\frac{e}{e-1}$ without predictions as $\lambda \to 1$.

Robustness is not part of this statement. The conference paper also states that the algorithm is $\frac{1}{1 - e^{-(\lambda - 1/b)}}$-robust (its Theorem 2.3). The authors' later full version (arXiv:2407.17712, footnote to Theorem 2.3) says that this claim is incorrect and states the weaker robustness $\frac{1 + 1/b}{1 - e^{-(\lambda - 1/b)}}$ instead, whose proof rests on a new Lemma A.2 of that version.

## Proof sketch

The distribution is a truncated version of the classical $e/(e-1)$ distribution. The expected cost against every number of days $x$ is computed by summing the geometric series; when $x$ and $y$ lie on the same side of $b$ this gives ratio at most $\frac{\lambda}{1 - e^{-\lambda}}$, and when they lie on different sides the extra cost is charged to $\eta = |x - y|$ as in the deterministic case.

## Depends on

- [Ski rental with a predicted number of days](ski-rental-with-prediction.md)
- [Consistency and robustness of learning-augmented online algorithms](../learning-augmented-caching/consistency-and-robustness.md)

## Proof depends on

- [Deterministic ski rental with a prediction](ski-rental-deterministic-with-prediction.md)

## Sources

- Manish Purohit, Zoya Svitkina, Ravi Kumar, "Improving Online Algorithms via ML Predictions", NeurIPS (2018), Algorithm 3 and Theorem 2.3.
- Ravi Kumar, Manish Purohit, Zoya Svitkina, "Improving Online Algorithms via ML Predictions", full version, arXiv:2407.17712 (2024), Algorithm 3, Theorem 2.3 and its footnote, and Lemma A.2.
