# Equivalent reward functions

Two reward functions are equivalent when they differ by a function of the prompt alone. Preference models and KL-regularized optimal policies see a reward only up to this equivalence.

Let $X$ be a set of prompts and $Y$ a set of responses. Rewards $r, r' : X \times Y \to \mathbb{R}$ are **equivalent** if there is a function $f : X \to \mathbb{R}$ with

$$r(x,y) - r'(x,y) = f(x) \qquad \text{for all } x \in X,\ y \in Y.$$

This is an equivalence relation on rewards, and it partitions the set of rewards into equivalence classes.

## Depends on

None.

## Proof depends on

None.

## Expansion

Reflexivity, symmetry and transitivity follow from those of equality of functions of $x$ ($f = 0$, $-f$, $f_1 + f_2$). Under the [Bradley–Terry and Plackett–Luce models](bradley-terry-and-plackett-luce-models.md) equivalent rewards give the same preferences ([lemma](equivalent-rewards-give-equal-preferences.md)), and under KL-regularized reward maximization they give the same optimal policy ([lemma](equivalent-rewards-give-equal-optimal-policies.md)). So a reward is identifiable from preferences at best up to its class, and only the class matters for the optimal policy; direct preference optimization picks one canonical member of each class ([reward reparameterization](reward-reparameterization-by-optimal-policy.md)).

## Sources

- R. Rafailov, A. Sharma, E. Mitchell, C. D. Manning, S. Ermon and C. Finn, *Direct Preference Optimization: Your Language Model is Secretly a Reward Model*, Advances in Neural Information Processing Systems 36 (NeurIPS 2023), doi:10.52202/075280-2338, Section 5.1, the definition preceding Lemma 1. [publisher page](https://proceedings.neurips.cc/paper_files/paper/2023/hash/a85b405ed65c6477a4fe8302b5e06ce7-Abstract-Conference.html)
