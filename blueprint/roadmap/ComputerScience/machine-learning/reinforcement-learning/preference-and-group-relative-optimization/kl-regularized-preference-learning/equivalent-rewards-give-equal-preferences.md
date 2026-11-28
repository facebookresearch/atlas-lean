# Equivalent rewards induce the same preferences

Under the Plackett–Luce model, and in particular under the Bradley–Terry model, two equivalent rewards induce the same distribution over rankings, so preference data cannot distinguish rewards within an equivalence class.

Let $r, r' : X \times Y \to \mathbb{R}$ be [equivalent rewards](equivalent-reward-functions.md), $r'(x,y) = r(x,y) + f(x)$, and let $p_r$ and $p_{r'}$ be the [Plackett–Luce models](bradley-terry-and-plackett-luce-models.md) they define. Then for every prompt $x$, every $K \ge 2$, all responses $y_1, \dots, y_K$ and every ranking $\tau$,

$$p_{r'}(\tau \mid y_1, \dots, y_K, x) = p_r(\tau \mid y_1, \dots, y_K, x).$$

In particular $p_{r'}(y_1 \succ y_2 \mid x) = p_r(y_1 \succ y_2 \mid x)$ for the Bradley–Terry model ($K = 2$).

## Depends on

- [Bradley–Terry and Plackett–Luce preference models](bradley-terry-and-plackett-luce-models.md)
- [Equivalent reward functions](equivalent-reward-functions.md)

## Proof depends on

None.

## Expansion

Every exponential in the $k$-th factor of the Plackett–Luce product gains the same factor $e^{f(x)}$, which cancels between numerator and denominator; the product is unchanged. Rafailov et al. note that this is the well-known under-specification of the Plackett–Luce family: maximum-likelihood estimates of a reward need additional identifiability constraints.

## Sources

- R. Rafailov, A. Sharma, E. Mitchell, C. D. Manning, S. Ermon and C. Finn, *Direct Preference Optimization: Your Language Model is Secretly a Reward Model*, Advances in Neural Information Processing Systems 36 (NeurIPS 2023), doi:10.52202/075280-2338, Lemma 1 (Section 5.1), with proof in Appendix A.5 of the supplementary material. [publisher page](https://proceedings.neurips.cc/paper_files/paper/2023/hash/a85b405ed65c6477a4fe8302b5e06ce7-Abstract-Conference.html)
