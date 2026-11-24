# Weil–Deligne representation of an ℓ-adic representation

Let $K$ be a finite extension of $\mathbb{Q}_p$ and $\ell \ne p$ a prime. Fix a lift $\varphi \in W_K$ of the
geometric Frobenius and a continuous surjective homomorphism $t \colon I_K \to \mathbb{Z}_\ell$. Then for every
continuous representation $\rho$ of $G_K$ on a finite-dimensional $\overline{\mathbb{Q}}_\ell$-vector space $V$
there is a unique Weil–Deligne representation $\mathrm{WD}(V, \rho) = (V, r, N)$ of $W_K$ over
$\overline{\mathbb{Q}}_\ell$ such that

$$\rho(\varphi^n \sigma) = r(\varphi^n \sigma) \exp\bigl(t(\sigma) N\bigr) \qquad (n \in \mathbb{Z}, \ \sigma \in I_K).$$

Up to natural isomorphism, $\mathrm{WD}$ does not depend on the choices of $\varphi$ and $t$, and $(V, \rho) \mapsto
\mathrm{WD}(V, \rho)$ is an equivalence of categories from continuous representations of $G_K$ on
finite-dimensional $\overline{\mathbb{Q}}_\ell$-vector spaces onto the **bounded** Weil–Deligne representations,
those for which, for some (equivalently every) $\sigma \in W_K \smallsetminus I_K$, all eigenvalues of $r(\sigma)$ are
$\ell$-adic units. The semisimplification of $\rho|_{W_K}$ is $r^{\mathrm{ss}}$. The functor commutes with
restriction to open subgroups and with tensor operations. Through an isomorphism
$\iota \colon \overline{\mathbb{Q}}_\ell \cong \mathbb{C}$ one obtains complex Weil–Deligne representations
$\iota\mathrm{WD}(V, \rho)$.

## Depends on

- [Weil–Deligne representations](weil-deligne-representations.md)
- [Weil group of a p-adic field](weil-group-of-a-p-adic-field.md), for $W_K$, $I_K$ and the geometric Frobenius

## Proof depends on

- [Grothendieck's ℓ-adic monodromy theorem](grothendieck-l-adic-monodromy-theorem.md), for the existence of $N$: an open subgroup of $I_K$ acts unipotently
- [Inertia and tame inertia of a p-adic field](inertia-and-tame-inertia-of-a-p-adic-field.md), for the factorization of $t$ through $I_K/P_{K,\ell} \cong T_\ell(\mu(\bar k))$ and the conjugation relation that gives $r(\sigma) N r(\sigma)^{-1} = \lvert \sigma \rvert N$

## Sources

- R. Taylor and T. Yoshida, "Compatibility of local and global Langlands correspondences", J. Amer. Math.
  Soc. 20 (2007), arXiv:math/0412357 (version 2), §1, p. 3 (bounded Weil–Deligne representations, the
  equivalence $(V, r, N) \mapsto (V, \rho)$ with $\rho(\varphi^n \sigma) = r(\varphi^n \sigma) \exp(t(\sigma) N)$, its
  independence of $t$ and $\varphi$, $\rho|_{W_K}^{\mathrm{ss}} \cong r^{\mathrm{ss}}$, citing Tate's Corvallis article,
  §4, and Deligne, §8), and p. 4 (compatibility with restriction and tensor operations).
- J.-M. Fontaine and Y. Ouyang, *Theory of p-adic Galois Representations*, book draft (PDF of 2022-05-26),
  archived at <http://web.archive.org/web/20261014003209/http://staff.ustc.edu.cn/~yiouyang/galoisrep.pdf>:
  §2.3.2, Definition 2.29 and Theorem 2.30 (the equivalence between potentially semistable $\ell$-adic
  representations and pairs $(D, N)$), and Example 2.35 (the fully faithful functor
  $V \mapsto (D_\ell(V), N)$ to representations of the Weil–Deligne group), for representations over
  $\mathbb{Q}_\ell$.
- T. Barnet-Lamb, T. Gee, D. Geraghty and R. Taylor, "Potential automorphy and change of weight", Ann. of
  Math. 179 (2014), arXiv:1010.2561 (version 2), Notation, p. 8 (the notation $\mathrm{WD}(\rho)$, citing
  Taylor–Yoshida, §1).
- Provenance: L. Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  attaches Weil–Deligne representations to $\ell$-adic representations at places not above $\ell$ as
  `GlobalTheory.WeilDeligne.wdOf`.
