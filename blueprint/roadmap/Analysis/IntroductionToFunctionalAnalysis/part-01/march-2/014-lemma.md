---
article_id: af_f9d7f0b9d7cdb8152d12b82f
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: HahnBanach.hahn_banach_one_step_extension_bound
---

# Lemma (March 2, 2021 lecture)

Let $V$ be a normed space, and let $M \subset V$ be a subspace. Let $u: M \to \mathbb{C}$ be linear with $|u(t)| \leq C||t||$ for all $t \in M$. If $x \not\in M$, then there exists a function $u'': M'' \to \mathbb{C}$ which is linear on the space $M'' = M + \mathbb{C} x = \{t + ax \mid t \in M, a \in \mathbb{C}\}$, with $u''|_M = u$ and $|u''(t'')| \leq C|t''|$ for all $t'' \in M''$.

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.102 Introduction to Functional Analysis (Spring 2021), March 2, 2021 lecture](../../../../../sources/v1/IntroductionToFunctionalAnalysis.md)
