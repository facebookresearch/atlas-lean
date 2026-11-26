# Sen's theorem on C-admissible representations

This node is still to be broken down. Let $K$ be a $p$-adic field in the sense of Fontaine–Ouyang, a complete
discretely valued field of characteristic $0$ whose residue field is perfect of characteristic $p$ (for instance a
finite extension of $\mathbb{Q}_p$), $\bar K$ an algebraic closure with completion $C$, $K^{\mathrm{ur}}$ the
maximal unramified extension of $K$ in $\bar K$ and $I_K = \operatorname{Gal}(\bar K/K^{\mathrm{ur}})$ the inertia
subgroup of $G_K$. A $p$-adic representation $\rho \colon G_K \to \operatorname{Aut}_{\mathbb{Q}_p}(V)$ is
**$C$-admissible** if it is [$B$-admissible](../admissible-representations.md) for $B = C$, that is, if
$C \otimes_{\mathbb{Q}_p} V \cong C^{\dim V}$ as a $C$-semilinear representation of $G_K$. Then $V$ is
$C$-admissible if and only if $\rho(I_K)$ is finite, that is, $\ker \rho \cap I_K$ is open in $I_K$.

A [Hodge–Tate representation](../hodge-tate-representations.md) is $C$-admissible exactly when its Hodge–Tate
numbers $h_i$ vanish for $i \ne 0$, since $C \otimes_{\mathbb{Q}_p} V \cong \bigoplus_i C(i)^{h_i}$. In dimension
$1$, for $V = \mathbb{Q}_p(\eta)$, the statement is Tate's, the case of the
[Tate–Sen theorem](../tate-sen-theorem.md) on $C(\eta)^{G_K}$.

A good expansion has pages for: the Sen operator $\Theta$ of a $C$-representation of $G_K$, from the
decompletion along the cyclotomic $\mathbb{Z}_p$-extension, and the classification of $C$-representations by it
(a $C$-representation is trivial exactly when $\Theta = 0$); and Sen's theorem that for a $p$-adic representation
$\Theta = 0$ exactly when $\rho(I_K)$ is finite.

## Depends on

- [Admissible representations for a regular ring of periods](../admissible-representations.md), for $C$-admissibility

## Proof depends on

Its proof uses the inputs listed in the expansion note.

## Sources

- J.-M. Fontaine and Y. Ouyang, *Theory of p-adic Galois Representations*, book draft (PDF of 2022-05-26),
  archived at <http://web.archive.org/web/20261014003209/http://staff.ustc.edu.cn/~yiouyang/galoisrep.pdf>: Remark 4.15, (4.8), p. 95 ($V$ is $\widehat{K^{\mathrm{ur}}}$-admissible exactly when $\ker \rho \cap I_K$ is
  open in $I_K$); §4.3.5, p. 105, Proposition 4.43 (Sen: "$\Theta = 0$ if and only if $\rho(I_K)$ is finite") and
  Proposition 4.44 ("A $p$-adic representation $V$ of $G_K$ is $C$-admissible if and only if the action of $I_K$ on
  $V$ is discrete, i.e. $V$ is $P$-admissible"), with Corollary 4.45, the case of dimension $1$; Theorem 4.40 and
  Corollary 4.41 (the Sen operator), and §4.4 (Sen's theorem, Theorem 4.47, from which Proposition 4.43 follows).
