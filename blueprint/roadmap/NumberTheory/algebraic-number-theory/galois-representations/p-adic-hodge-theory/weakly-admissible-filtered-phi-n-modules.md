# Weakly admissible filtered (φ, N)-modules

Let $K$ be a $p$-adic field in the sense of Fontaine–Ouyang, a complete discretely valued field of characteristic $0$ whose residue field is perfect of characteristic $p$ (for instance a finite extension of $\mathbb{Q}_p$), with maximal absolutely unramified subfield $K_0$ and absolute
Frobenius $\sigma$ of $K_0$. A **$(\varphi, N)$-module** over $K_0$ is a finite-dimensional $K_0$-vector space $D$
with a bijective $\sigma$-semilinear map $\varphi \colon D \to D$ and a $K_0$-linear map $N \colon D \to D$ with
$N \varphi = p \varphi N$; such an $N$ is nilpotent. It is **filtered** if $D_K = K \otimes_{K_0} D$ carries a
decreasing, separated and exhaustive filtration by $K$-subspaces. For such $D$ of dimension $r$:

- the **Newton number** $t_N(D)$ is $v_p(\lambda)$, where $\varphi$ acts on $\bigwedge^r D$ as $x \mapsto \lambda \sigma(x)$
  in a basis (well defined since $v_p(\sigma(\mu)/\mu) = 0$), $v_p$ normalized by $v_p(p) = 1$;
- the **Hodge number** $t_H(D)$ is $\sum_{i \in \mathbb{Z}} i \dim_K \operatorname{gr}^i D_K$.

$D$ is **weakly admissible** (called *admissible* in Fontaine–Ouyang's terminology) if $t_H(D) = t_N(D)$ and
$t_H(D') \le t_N(D')$ for every sub-$K_0$-space $D' \subseteq D$ stable under $\varphi$ and $N$, with the induced
filtration on $D'_K$. The weakly admissible filtered $(\varphi, N)$-modules form an abelian category; those with
$N = 0$ are the weakly admissible filtered $\varphi$-modules.

## Depends on

This node has no prerequisites.

## Proof depends on

This node has no prerequisites.

## Sources

- J.-M. Fontaine and Y. Ouyang, *Theory of p-adic Galois Representations*, book draft (PDF of 2022-05-26),
  archived at <http://web.archive.org/web/20261014003209/http://staff.ustc.edu.cn/~yiouyang/galoisrep.pdf>:
  §8.2, Definition 8.13 ($(\varphi, N)$-modules), Proposition 8.17 ($N$ nilpotent), Definitions 8.18 and 8.20
  ($t_N$), Definition 8.34 (filtered $(\varphi, N)$-modules), Definition 8.36 ($t_H$), Definition 8.39
  (admissible) and Proposition 8.41 (the abelian category); Remark 8.55 (the old terminology "weakly
  admissible").
