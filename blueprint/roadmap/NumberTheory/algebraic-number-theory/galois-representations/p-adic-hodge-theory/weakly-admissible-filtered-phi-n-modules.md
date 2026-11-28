# Weakly admissible filtered (φ, N)-modules

Let $K_0$ be a field with a ring automorphism $\sigma$, let $p \in K_0$, let $K$ be a field extension of $K_0$, and let $v$ be an additive valuation of $K_0$ with values in $\mathbb{Z} \cup \{\infty\}$. A **$(\varphi, N)$-module** over $K_0$ is a $K_0$-vector space $D$
with a bijective $\sigma$-semilinear map $\varphi \colon D \to D$ and a $K_0$-linear map $N \colon D \to D$ with
$N \varphi = p \varphi N$. It is **filtered** if $D_K = K \otimes_{K_0} D$ carries a decreasing, separated and
exhaustive filtration by $K$-subspaces, indexed by $\mathbb{Z}$. For such $D$ of finite dimension:

- the **Newton number** $t_N(D)$ is $v(\det A)$, where $A$ is the matrix of $\varphi$ in a fixed basis of $D$; when
  $v \circ \sigma = v$, as in the setting below, it does not depend on the basis;
- the **Hodge number** $t_H(D)$ is $\sum_{i \in \mathbb{Z}} i \dim_K \operatorname{gr}^i D_K$.

$D$ is **weakly admissible** if $t_H(D) = t_N(D)$ and $t_H(D') \le t_N(D')$ for every sub-$K_0$-space
$D' \subseteq D$ stable under $\varphi$ and $N$, with the induced filtration on $D'_K$. Those with $N = 0$ are the
weakly admissible filtered $\varphi$-modules.

In the setting of Fontaine–Ouyang, $K$ is a $p$-adic field, a complete discretely valued field of characteristic $0$
whose residue field is perfect of characteristic $p$ (for instance a finite extension of $\mathbb{Q}_p$), $K_0$ is
its maximal absolutely unramified subfield, $\sigma$ is the absolute Frobenius of $K_0$, $p$ is the prime, and $v$
is the $p$-adic valuation, normalized by $v(p) = 1$. There, for $D$ of finite dimension (as their Definition 8.13
requires), $N$ is nilpotent, weakly admissible modules are what Fontaine–Ouyang call *admissible*, and they form an
abelian category.

## Sources

- J.-M. Fontaine and Y. Ouyang, *Theory of p-adic Galois Representations*, book draft (PDF of 2022-05-26),
  archived at <http://web.archive.org/web/20261014003209/http://staff.ustc.edu.cn/~yiouyang/galoisrep.pdf>:
  §8.2, Definition 8.13 ($(\varphi, N)$-modules), Proposition 8.17 ($N$ nilpotent), Definitions 8.18 and 8.20 and Proposition 8.21
  ($t_N$), Definition 8.34 (filtered $(\varphi, N)$-modules), Definition 8.36 ($t_H$), Definition 8.39
  (admissible) and Proposition 8.41 (the abelian category); Remark 8.55 (the old terminology "weakly
  admissible").
