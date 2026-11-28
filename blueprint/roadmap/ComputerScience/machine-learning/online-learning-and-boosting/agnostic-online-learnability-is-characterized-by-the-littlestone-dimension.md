# Agnostic online learnability is characterized by the Littlestone dimension

For a nonempty class $H$ of binary classifiers and a horizon $T$, let $R_H(T)$ be the infimum, over randomized online
learners that may depend on $T$, of the worst-case expected regret over sequences of length $T$, against an oblivious
adversary, under the protocol of the online-classification page. Call $H$ agnostically online learnable if
$R_H(T) = o(T)$, that is, if for every horizon $T$ some learner for that horizon has worst-case expected regret at most
$r(T)$, with $r(T)/T \to 0$. Then $H$ is agnostically online learnable if and only if its Littlestone dimension is
finite (Ben-David, Pál and Shalev-Shwartz). The two directions are the regret upper bound for finite dimension, by a
learner that receives the horizon $T$ as input, and the linear lower bound for infinite dimension, which holds for
every learner at every horizon.

## Depends on

- [Online classification protocol, mistakes and regret](online-classification-protocol-mistakes-and-regret.md)

## Proof depends on

- [Agnostic online learning with Littlestone dimension](agnostic-online-learning-with-littlestone-dimension.md)

## Sources

- Understanding Machine Learning: From Theory to Algorithms — Shalev-Shwartz, Ben-David / Cambridge University Press, Theorem 21.10 and its proof. <https://www.cs.huji.ac.il/~shais/UnderstandingMachineLearning/understanding-machine-learning-theory-algorithms.pdf>
- S. Ben-David, D. Pál and S. Shalev-Shwartz, *Agnostic online learning*, COLT 2009, Theorem 1 and the lower bound of Section 3. <https://home.ttic.edu/~shai/papers/Ben-DavidPalShalev09.pdf>
