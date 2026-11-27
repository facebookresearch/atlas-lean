# Vapnik-Chervonenkis inequality: uniform convergence from the growth function

Let $Z$ be a countable set with all subsets measurable, $G$ a class of functions $Z \to \{0,1\}$ with growth function $\Pi_G$, $\mu$ a probability measure on $Z$, $m \ge 1$ and $\varepsilon > 0$. Then

$$
\mu^m\Big(\Big\{S : \exists g \in G,\ \Big|\tfrac{1}{m}\#\{i : g(S_i) = 1\} - \mu(g = 1)\Big| \ge \varepsilon\Big\}\Big) \le 4\,\Pi_G(2m)\, e^{-m\varepsilon^2/8}.
$$

Applied to the 0-1 loss class of a binary concept class $C$ on a countable domain, the probability that $m$ i.i.d. labelled examples are not $\varepsilon$-representative for $C$ is at most $4\,\Pi_C(2m)\, e^{-m\varepsilon^2/8}$. If every finite set shattered by $C$ has at most $d$ points and $\varepsilon, \delta \in (0,1)$, then

$$
m \ge \frac{16}{\varepsilon^2}\Big(2d \ln\frac{10}{\varepsilon} + \ln\frac{4}{\delta}\Big)
$$

examples are $\varepsilon$-representative with probability at least $1 - \delta$.

## Proof sketch

By the ghost-sample step, the bad event has probability at most twice that of the double-sample event that some $g$ has counts on the two halves differing by at least $m\varepsilon/2$ (a second independent sample is close to $\mu$ with probability at least $1/2$ once $4e^{-m\varepsilon^2/2} \le 1$). For a fixed double sample only $\Pi_G(2m)$ restrictions of $G$ matter, and for each, Hoeffding's inequality over random swaps bounds the fraction of bad swaps by $2e^{-m\varepsilon^2/8}$; swap counting finishes. Sauer's lemma converts the growth function into the explicit sample size.

## Depends on

- [Growth function](../../../../not-yet-classified/growth-function/growth-function.md)
- [Uniform convergence property and eps-representative samples](../../agnostic-pac-learning-and-uniform-convergence/uniform-convergence-property-and-eps-representative-samples.md)
- [The VC dimension is at most the size of the ground set](../../../../../Combinatorics/extremal-set-theory/vc-dim-le-card.md)

## Proof depends on

- [Double-sample symmetrization: ghost samples and coordinate swaps](double-sample-symmetrization.md)
- [Sauer bound for the growth function](../../../../not-yet-classified/growth-function/growth-function-le-sum.md)
- [Two-sided Hoeffding inequality for averages of bounded variables](../../../../../Probability/concentration-inequalities/hoeffding-s-inequality/measure-real-abs-avg-sub-ge-le.md)

## Sources

- V. N. Vapnik and A. Ya. Chervonenkis, "On the Uniform Convergence of Relative Frequencies of Events to Their Probabilities", Theory of Probability and Its Applications, 1971.
- M. Anthony and P. L. Bartlett, "Neural Network Learning: Theoretical Foundations", Cambridge University Press, 1999.
