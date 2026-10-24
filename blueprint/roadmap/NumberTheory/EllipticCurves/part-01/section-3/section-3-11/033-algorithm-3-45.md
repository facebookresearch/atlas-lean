---
article_id: af_ab275bb5dda94b5c7f759ae9
declaration: def
origin: cited
statement: formalized
lean: BerlekampRabin.berlekampRabinAlgorithm
---

# Algorithm 3.45

Given a monic polynomial $f \in \mathbb{F}_{q}[x]$, output an element $r \in \mathbb{F}_{q}$ such that $f(r)=0$, or null if no such $r$ exists.
1. If $f(0)=0$ then return 0.
2. Compute $g=\operatorname{gcd}\left(f, x^{q}-x\right)$.
3. If $\operatorname{deg} g=0$ then return null.
4. While $\operatorname{deg} g>1$:
   a. Pick a random $\delta \in \mathbb{F}_{q}$.
   b. Compute $h=\operatorname{gcd}\left(g,(x+\delta)^{s}-1\right)$.
   c. If $0\lt \operatorname{deg} h\lt \operatorname{deg} g$ then replace $g$ by $h$ or $g/h$, whichever has lower degree.
5. Return $r$, where $g(x)=x-r$.

## Depends on

- [Definition 3.4](../section-3-1/007-definition-3-4.md)

## Proof depends on

- [Theorem 3.44 (Rabin 1980)](032-rabin-1980.md)

## Sources

- [MIT 18.783 Elliptic Curves (Spring 2021), Section 3.11](../../../../../../sources/v1/EllipticCurves.md)
