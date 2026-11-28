# Agnostic online learnability is characterized by the Littlestone dimension

Call a nonempty class $H$ of binary classifiers agnostically online learnable if some randomized online learner has
expected regret $o(T)$ in the worst case over sequences of length $T$, against an oblivious adversary, under the
protocol of the online-classification page. Then $H$ is agnostically online learnable if and only if its
Littlestone dimension is finite (Ben-David, Pál and Shalev-Shwartz). The two directions are the regret upper bound
for finite dimension and the linear lower bound for infinite dimension.

## Depends on

- [Online classification protocol, mistakes and regret](online-classification-protocol-mistakes-and-regret.md)

## Proof depends on

- [Agnostic online learning with Littlestone dimension](agnostic-online-learning-with-littlestone-dimension.md)

## Sources

- Understanding Machine Learning: From Theory to Algorithms — Shalev-Shwartz, Ben-David / Cambridge University Press, Theorem 21.10 and its proof. <https://www.cs.huji.ac.il/~shais/UnderstandingMachineLearning/understanding-machine-learning-theory-algorithms.pdf>
- S. Ben-David, D. Pál and S. Shalev-Shwartz, *Agnostic online learning*, COLT 2009, Theorem 1 and the lower bound of Section 3. <https://home.ttic.edu/~shai/papers/Ben-DavidPalShalev09.pdf>
