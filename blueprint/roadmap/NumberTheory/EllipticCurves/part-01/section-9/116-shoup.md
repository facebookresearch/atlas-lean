---
article_id: af_4429e5b8f332c8996fda050a
declaration: theorem
origin: cited
lean: shoup_theorem_9_7_general_N
---

# Theorem 9.7 (Shoup)

Let $G = \langle\alpha\rangle$ be a group of order $N$. Let $B$ be a black
 box for $G$ supporting the operations identity, inverse, and compose, using
 a random identification map $\operatorname{id}: G \hookrightarrow
 \{0,1\}^m$. Let $A: \{0,1\}^m \times \{0,1\}^m \rightarrow
 \mathbb{Z}/N\mathbb{Z}$ be a randomized generic group algorithm that makes
 at most $s - 4\lceil \lg N \rceil$ calls to $B$, for some integer $s$, and
 let $x$ denote a random element of $\mathbb{Z}/N\mathbb{Z}$. Then $\Pr_{x,
 \operatorname{id}, \tau}[A(\operatorname{id}(\alpha),
 \operatorname{id}(x\alpha)) = x] < s^{2}/(2p)$, where $\tau$ denotes the
 random coin-flips made by $A$ and $p$ is the largest prime factor of $N$.

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.783 Elliptic Curves (Spring 2021), Section 9.13](../../../../../sources/v1/EllipticCurves.md)
