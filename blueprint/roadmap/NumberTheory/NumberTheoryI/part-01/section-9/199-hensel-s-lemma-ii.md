---
article_id: af_5accda5c17040e594b93056f
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: hensel_newton_valuation_full
---

# Lemma 9.16 (Hensel's Lemma II)

Let $A$ be a complete DVR. Let $f \in A[x]$, and suppose $a_{0} \in A$ satisfies $|f(a_{0})| < |f'(a_{0})|^{2}$ (so in particular, $f'(a_{0})$ divides $f(a_{0})$), and for $n \geq 0$ define $a_{n+1}\coloneqq a_{n}-f(a_{n})/f'(a_{n})$. The sequence $(a_{n})$ is well-defined and converges to the unique root $a \in A$ of $f$ for which $|a-a_{0}| \leq \epsilon\coloneqq |f(a_{0})|/|f'(a_{0})|^{2}$. Moreover, $|f(a_{n})| \leq \epsilon^{2^{n}}|f'(a_{0})|^{2}$ for all $n \geq 0$.

## Depends on

- [Definition 1.10](../section-1/section-1-4/008-definition-1-10.md)
- [Definition 8.1](../section-8/172-definition-8-1.md)
- [Definition 9.10](194-definition-9-10.md)

## Proof depends on

- [Lemma 9.11](195-lemma-9-11.md)

## Sources

- [MIT 18.785 Number Theory I (Fall 2021), Section 9.2](../../../../../sources/v1/NumberTheoryI.md)
