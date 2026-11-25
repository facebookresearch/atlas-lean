# Weil–Deligne representations

Let $K$ be a finite extension of $\mathbb{Q}_p$ with Weil group $W_K$, and $\Omega$ an algebraically closed
field of characteristic $0$ (for instance $\mathbb{C}$ or $\overline{\mathbb{Q}}_\ell$). A **Weil–Deligne
representation** of $W_K$ over $\Omega$ is a triple $(V, r, N)$ of a finite-dimensional $\Omega$-vector space
$V$, a homomorphism $r \colon W_K \to \operatorname{GL}(V)$ whose kernel is open (equivalently, contains an open
subgroup of $I_K$), and an endomorphism $N \in \operatorname{End}(V)$ with

$$r(\sigma) N r(\sigma)^{-1} = \lvert \mathrm{Art}_K^{-1}(\sigma) \rvert_K \, N \qquad (\sigma \in W_K),$$

where $\mathrm{Art}_K \colon K^\times \cong W_K^{\mathrm{ab}}$ sends uniformizers to geometric Frobenius elements, so
the right-hand side is $q^{-m} N$ for $\sigma$ above the $m$-th power of the geometric Frobenius. Such an $N$
is nilpotent. Morphisms are linear maps commuting with $r$ and $N$.

- $(V, r, N)$ is **Frobenius semisimple** if $r$ is semisimple. Its **Frobenius semisimplification**
  $(V, r, N)^{F\text{-ss}} = (V, r^{\mathrm{ss}}, N)$ is defined by choosing a lift $\varphi \in W_K$ of the
  geometric Frobenius, writing $r(\varphi) = su = us$ with $s$ semisimple and $u$ unipotent, and setting
  $r^{\mathrm{ss}}(\varphi^n \sigma) = s^n r(\sigma)$ for $n \in \mathbb{Z}$ and $\sigma \in I_K$; it is
  independent of the choices and Frobenius semisimple.
- The **tensor product** of $(V_1, r_1, N_1)$ and $(V_2, r_2, N_2)$ is
  $(V_1 \otimes V_2, r_1 \otimes r_2, N_1 \otimes 1 + 1 \otimes N_2)$; the internal $\operatorname{Hom}$ is
  $\operatorname{Hom}(V_1, V_2)$ with $(r(w)f)(v) = r_2(w) f(r_1(w)^{-1} v)$ and $Nf = N_2 f - f N_1$, and the
  **contragredient** $(V, r, N)^\vee$ is the $\operatorname{Hom}$ into the trivial one-dimensional representation.
  The **determinant** of $(V, r, N)$ is the character $\det \circ r$ of $W_K$.
- For a finite extension $K'/K$, the restriction is $(V, r|_{W_{K'}}, N)$.

## Depends on

- [Weil group of a p-adic field](weil-group-of-a-p-adic-field.md), for $W_K$, $I_K$, the geometric Frobenius and $\mathrm{Art}_K$

## Proof depends on

- [Weil group of a p-adic field](weil-group-of-a-p-adic-field.md), for the exact sequence $1 \to I_K \to W_K \to \mathbb{Z} \to 1$ and $\lvert w \rvert = q^{-m}$ for $w$ above the $m$-th power of the geometric Frobenius: they give the nilpotence of $N$, which maps the generalized $\lambda$-eigenspace of $r(\varphi)$ into the generalized $q^{-1}\lambda$-eigenspace, the Frobenius semisimplification, and, through $W_{K'} = W_K \cap G_{K'}$ and $\lvert w \rvert_{K'} = \lvert w \rvert_K$ for $w \in W_{K'}$, the restriction

## Sources

- R. Taylor and T. Yoshida, "Compatibility of local and global Langlands correspondences", J. Amer. Math.
  Soc. 20 (2007), arXiv:math/0412357 (version 2), §1, p. 3 (the definition over an algebraically closed field
  $\Omega$ of characteristic $0$ with the relation $r(\sigma) N r(\sigma)^{-1} = \lvert \mathrm{Art}_K^{-1}(\sigma) \rvert_K N$,
  restriction, Frobenius semisimplicity and the Frobenius semisimplification).
- T. Wedhorn, "The local Langlands correspondence for GL(n) over p-adic fields", arXiv:math/0011210
  (version 2): (3.1.1), (3.1.6) Definition (with (3.1.6.1) and Frobenius semisimplicity), (3.1.7) Remark ($N$ is
  nilpotent), (3.1.8) (tensor products, $\operatorname{Hom}$ and the contragredient), (3.1.9)–(3.1.10) (the Weil–Deligne
  group and $W_K \times \operatorname{SL}_2(\mathbb{C})$), over $\mathbb{C}$.
- J.-M. Fontaine and Y. Ouyang, *Theory of p-adic Galois Representations*, book draft (PDF of 2022-05-26),
  archived at <http://web.archive.org/web/20261014003209/http://staff.ustc.edu.cn/~yiouyang/galoisrep.pdf>:
  §2.3.3, Definition 2.33 and Remark 2.34 (written with $\tau_k$ and $a(w)$ defined by
  $w|_{\bar k} = \tau_k^{a(w)}$ and the relation $N \rho(w) = q^{a(w)} \rho(w) N$; this page follows the
  normalization of Taylor–Yoshida and Wedhorn, through $\mathrm{Art}_K$).
- Provenance: L. Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  works with Weil–Deligne representations at the completions of number fields as
  `GlobalTheory.WeilDeligne.WD`.
