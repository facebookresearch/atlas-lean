# Grothendieck's ℓ-adic monodromy theorem

Let $K$ be a finite extension of $\mathbb{Q}_p$ with inertia group $I_K$, let $\ell \ne p$ be a prime, and let
$\rho \colon G_K \to \operatorname{GL}(V)$ be an $\ell$-adic representation, that is, a continuous linear action of
$G_K$ on a finite-dimensional $\mathbb{Q}_\ell$-vector space $V$. Then some open subgroup of $I_K$ acts
unipotently on $V$; equivalently, $V$ is **potentially semistable**: there is a finite extension $K'/K$ in
$\bar K$ such that $I_{K'}$ acts unipotently on $V$, that is, the semisimplification of $V|_{G_{K'}}$ is
unramified.

More precisely, choose a topological generator $t$ of $I_K/P_{K,\ell} \cong T_\ell(\mu(\bar k))$. After a finite
extension of $K$ the action of $G_K$ factors through $G_{K,\ell}$, and some power $t^N$, $N \ge 1$, acts
unipotently.

## Depends on

- [Inertia and tame inertia of a p-adic field](inertia-and-tame-inertia-of-a-p-adic-field.md), for $I_K$, $P_{K,\ell}$ and $G_{K,\ell}$

## Proof depends on

- [Inertia and tame inertia of a p-adic field](inertia-and-tame-inertia-of-a-p-adic-field.md), for $I_K/P_{K,\ell} \cong T_\ell(\mu(\bar k))$ and the relation $g t g^{-1} = t^{\chi_\ell(g)}$, which makes the eigenvalues of $\rho(t)$ roots of unity
- [Cyclotomic character and Tate twists](../cyclotomic-character-and-tate-twists.md), for the $\ell$-adic cyclotomic character, whose image is open in $\mathbb{Z}_\ell^\times$ because $K(\mu_\ell)$ contains only finitely many $\ell$-power roots of unity

## Sources

- J.-M. Fontaine and Y. Ouyang, *Theory of p-adic Galois Representations*, book draft (PDF of 2022-05-26),
  archived at <http://web.archive.org/web/20261014003209/http://staff.ustc.edu.cn/~yiouyang/galoisrep.pdf>:
  §2.3.1, Definition 2.24 (unramified, potentially good reduction, semistable, potentially semistable),
  Remark 2.25, and Theorem 2.26 with its proof ("any $\ell$-adic representation of $G_K$ is potentially
  semi-stable. In particular, this is the case if $k$ is finite"); Corollary 2.27 (the form for
  representations coming from algebraic geometry, Grothendieck's $\ell$-adic monodromy theorem).
- R. Taylor and T. Yoshida, "Compatibility of local and global Langlands correspondences", J. Amer. Math.
  Soc. 20 (2007), arXiv:math/0412357 (version 2), §1, p. 3, which cites Tate's Corvallis article, §4, and
  Deligne, §8, for the resulting Weil–Deligne representations.
