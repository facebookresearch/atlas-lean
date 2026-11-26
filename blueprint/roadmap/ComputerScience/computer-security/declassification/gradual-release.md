# Gradual release

A command $c$ of the [language with low events](attacker-knowledge.md) satisfies *gradual release* if for every low projection $M^0_L$ and every
$\vec\ell_n = \ell_1, \dots, \ell_n \in L(c, M^0_L)$ with $n \ge 1$, of which $\ell_{r_1}, \dots, \ell_{r_m}$ are all the release events (the low events produced by
$\mathrm{declassify}$ assignments),

$$\forall i.\ 1 \le i \le n \wedge (\forall j.\ r_j \ne i) \implies k_\downarrow(c, M^0_L, \vec\ell_{i-1}) = k_\downarrow(c, M^0_L, \vec\ell_i),$$

with $k_\downarrow(c, M^0_L, \vec\ell_0) = k(c, M^0_L)$. Knowledge may be refined only at release events. Gradual release is a policy on *where* information is
released, in contrast with what-policies such as [delimited release](../information-flow/delimited-release.md).

## Depends on

- [Attacker knowledge for programs with low events](attacker-knowledge.md)

## Sources

- A. Askarov and A. Sabelfeld, "Gradual release: unifying declassification, encryption and key release policies", *Proceedings of the 2007 IEEE Symposium on Security and Privacy*, copy at <https://www.cs.cornell.edu/~aslan/askarov-sabelfeld-sp07.pdf>: Section 2, Definition 2 (gradual release) and the discussion of the dimensions of declassification that follows it.
