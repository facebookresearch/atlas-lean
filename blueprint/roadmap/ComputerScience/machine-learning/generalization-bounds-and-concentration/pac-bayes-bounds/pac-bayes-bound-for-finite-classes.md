# PAC-Bayes bound for finite classes

Let $H$ be finite and nonempty, $\ell : H \times Z \to [0, 1]$, $m \ge 2$ and $\delta \in (0, 1)$. With probability at least $1 - \delta$ over $S \sim D^m$, every $h \in H$ satisfies

$$L_D(h) \le L_S(h) + \sqrt{\frac{\ln \lvert H \rvert + \ln(m/\delta)}{2(m - 1)}}.$$

## Proof

Apply the PAC-Bayes bound with the uniform prior $P$ and the point-mass posterior $Q = \delta_h$: $\mathrm{KL}(\delta_h \Vert P) = \ln(1 / P(h)) = \ln \lvert H \rvert$ and
$L(\delta_h) = L(h)$. The bound holds simultaneously for all posteriors, hence for all $h$.

## Depends on

- [PAC-Bayes bound (McAllester form)](pac-bayes-bound.md)

## Sources

- S. Shalev-Shwartz and S. Ben-David, *Understanding Machine Learning*, Cambridge University Press, 2014 (author copy), Theorem 31.1. <https://www.cs.huji.ac.il/~shais/UnderstandingMachineLearning/understanding-machine-learning-theory-algorithms.pdf>
